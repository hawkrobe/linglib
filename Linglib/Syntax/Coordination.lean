import Linglib.Features.Formative
import Linglib.Semantics.Coordination.Defs
import Linglib.Data.WALS.Features.F56A
import Linglib.Data.WALS.Features.F63A
import Linglib.Data.WALS.Features.F64A

/-!
# Coordination: morphosyntactic typology
[haspelmath-2007] [stassen-2000] [mitrovic-sauerland-2016]
[dryer-haspelmath-2013] [wals-2013]

Per-language typological substrate for coordination across three frameworks:

1. **[haspelmath-2007] structural typology**: syndesis (asyndetic /
   monosyndetic / bisyndetic), coordinator position, structural patterns,
   and diachronic source (comitative vs additive focus particle).
2. **[stassen-2000] AND/WITH typology**: derived from WALS Ch 63
   (lexical identity of "and" and "with").
3. **WALS Ch 56/63/64**: conjunction-quantifier relation, NP conjunction,
   nominal-vs-verbal conjunction.

Mirrors the `Linglib/Typology/{Possession,Negation,Question,Comparison}.lean`
substrate-extension pattern. Fragment-importable; cross-linguistic theorems
live in `Studies/Haspelmath2007.lean` (structural typology + 19-language
sample), `Studies/MitrovicSauerland2016.lean` (J/MU framework + M&S
generalisations), and `Studies/Stassen2000.lean` (AND/WITH typology + 15-
language WALS sample).

## Main declarations

* `Syndesis`, `CoordinatorPosition`, `CoordPattern`, `DiachronicSource` —
  Haspelmath structural enums.
* `AndWithStatus` — Stassen 2000 binary classification.
* `ConjQuantRelation`, `ConjComitativeRelation`, `NomVerbalConjRelation` —
  WALS Ch 56/63/64 aliases.
* `SourcedEntry`, `ConjunctionSystem` — per-language structs.
* `CoordinationProfile` — WALS profile bundle.
* `ConjunctionSystem.hasStrategy`, `muIsAdditive`, `hasSource`,
  `hasMonosyndetic`, `hasBisyndetic`, `muBoundness` — `Prop`-valued
  decidable predicates.

## Implementation notes

* Helper predicates are `Prop` with explicit `Decidable` instances rather
  than `Bool`-returning, so consumers can write `sys.hasStrategy s`
  directly in theorem statements without `= true` boilerplate while
  retaining `decide`-checkability over finite samples.
* `DiachronicSource` collapses Heine's full grammaticalization-source
  taxonomy to two main pathways relevant for coordination (comitative,
  focus particle); other pathways are conflated under `.other`.
* `AndWithStatus` is [stassen-2000]'s binary classification; some
  authors (e.g. Mauri 2008) argue for a finer multi-way split.
-/

namespace Syntax.Coordination

/-! ### [mitrovic-sauerland-2014] conjunction strategy -/

/-- Cross-linguistic conjunction strategy. [mitrovic-sauerland-2014] decompose DP
    conjunction into three semantic pieces: J (set intersection), MU (subset), and a
    type-shifter; languages vary in which pieces are overtly realized. -/
inductive ConjunctionStrategy where
  /-- Only J particle overt (e.g., English "and", Hungarian "es", Georgian "da"). -/
  | jOnly
  /-- Only MU particles overt (e.g., Japanese "mo...mo", Hungarian "is...is",
      Georgian "-c...-c"). -/
  | muOnly
  /-- Both J and MU overt (e.g., Hungarian "is es...is", Georgian "-c da...-c"). -/
  | jMu
  deriving DecidableEq, Repr

/-- Number of overt functional morphemes per strategy. Under [mitrovic-sauerland-2016] the
    underlying structure always has 3 pieces (J + MU1 + MU2); what varies is how many are
    pronounced. -/
def ConjunctionStrategy.overtMorphemeCount : ConjunctionStrategy → Nat
  | .jOnly  => 1
  | .muOnly => 2
  | .jMu    => 3

/-- Under [mitrovic-sauerland-2016] there are always 3 semantic pieces. -/
def ConjunctionStrategy.semanticPieceCount : Nat := 3

/-- [mitrovic-sauerland-2016] + Transparency Principle: more overt morphemes -> easier to
    acquire (closer to a 1-to-1 form-meaning mapping). -/
def ConjunctionStrategy.predictedTransparency : ConjunctionStrategy → Nat :=
  ConjunctionStrategy.overtMorphemeCount

/-! ### Haspelmath 2007 structural enums -/

/-- Syndesis: presence and number of overt coordinators ([haspelmath-2007] §1). -/
inductive Syndesis where
  /-- A B (juxtaposition, no overt linker). -/
  | asyndetic
  /-- A co-B (single coordinator). -/
  | monosyndetic
  /-- co-A co-B (two coordinators, one per coordinand). -/
  | bisyndetic
  deriving DecidableEq, BEq, Repr

/-- Coordinator position relative to its coordinand ([haspelmath-2007] §1.2).

    [haspelmath-2007] notes that **co-A B (prepositive on first
    coordinand only) is unattested** (cf. [stassen-2000], n=260). -/
inductive CoordinatorPosition where
  /-- co precedes coordinand: "and A" / English "both X". -/
  | prepositive
  /-- co follows coordinand: "A-and" / Latin "X-que". -/
  | postpositive
  deriving DecidableEq, BEq, Repr

/-- Structural pattern for binary coordination ([haspelmath-2007] (17)).

    Monosyndetic: 3 attested patterns (of 4 logically possible). The fourth
    monosyndetic pattern `co-A B` (prepositive on first coordinand only) is
    unattested per [stassen-2000], n=260; the absence is encoded as a
    theorem rather than by omission (see `Studies/Haspelmath2007.lean`).

    Bisyndetic: 4 attested patterns. -/
inductive CoordPattern where
  /-- A co-B: medial prepositive (English "A and B"). -/
  | a_co_b
  /-- A-co B: medial postpositive on 1st (Tibetan "A-daŋ B"). -/
  | a'co_b
  /-- A B-co: final postpositive (Latin "senatus populus-que"). -/
  | a_b'co
  /-- co-A B: prepositive on first coordinand only — typologically
      unattested for conjunction ([stassen-2000], n=260). -/
  | co'a_b
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
  | .a_co_b | .a'co_b | .a_b'co | .co'a_b => .monosyndetic
  | .co'a_co'b | .a'co_b'co | .a'co_co'b | .co'a_b'co => .bisyndetic

/-- Diachronic source of conjunction constructions ([haspelmath-2007] §5.1). -/
inductive DiachronicSource where
  /-- "with" → coordinator (gives A co-B or A-co B). -/
  | comitative
  /-- "also/too" → coordinator (gives A-co B-co). -/
  | focusParticle
  /-- Other or unknown source. -/
  | other
  deriving DecidableEq, BEq, Repr

/-- Haspelmath's link between diachronic source and structural syndesis.
    Returns the syndesis pattern expected from the source pathway; `none`
    for `.other` since we make no prediction there. -/
def DiachronicSource.expectedSyndesis : DiachronicSource → Option Syndesis
  | .comitative    => some .monosyndetic
  | .focusParticle => some .bisyndetic
  | .other         => none

/-! ### Stassen 2000 AND/WITH classification -/

/-- [stassen-2000] AND/WITH classification of languages.
    AND-languages have structurally distinct coordinate and comitative
    strategies. WITH-languages use comitative encoding as the only strategy
    for NP conjunction (lexical identity of "and" and "with"). -/
inductive AndWithStatus where
  /-- Coordinate and comitative are structurally distinct. -/
  | andLang
  /-- Comitative marker = coordinator. -/
  | withLang
  deriving DecidableEq, BEq, Repr

/-! ### WALS aliases (Chs 56/63/64) -/

/-- WALS Ch 56: conjunction-quantifier relation. -/
abbrev ConjQuantRelation := Data.WALS.F56A.ConjunctionsAndUniversalQuantifiers

/-- WALS Ch 63: noun-phrase conjunction (and-vs-with). -/
abbrev ConjComitativeRelation := Data.WALS.F63A.NounPhraseConjunction

/-- WALS Ch 64: nominal-vs-verbal conjunction. -/
abbrev NomVerbalConjRelation := Data.WALS.F64A.NominalAndVerbalConjunction

/-- Derive AND/WITH status from the conjunction-comitative relation
    ([stassen-2000]'s diagnostic). -/
def ConjComitativeRelation.toAndWithStatus :
    ConjComitativeRelation → AndWithStatus
  | .andDifferentFromWith => .andLang
  | .andIdenticalToWith   => .withLang

/-! ### Per-language structs -/

/-- A coordination entry annotated with its diachronic source.
    Wraps `Coordinator` (from `Semantics/Coordination/Defs`) with typological
    metadata. For languages with Fragment files, `entry` references the
    Fragment entry directly — no data duplication. -/
structure SourcedEntry where
  /-- The coordination morpheme entry. -/
  entry : Coordinator
  /-- Likely diachronic source, if known. -/
  source : Option DiachronicSource := none
  deriving Repr

/-- A language's conjunction system (M&S framework). -/
structure ConjunctionSystem where
  /-- Language name. -/
  language : String
  /-- Available conjunction morphemes (sourced entries). -/
  morphemes : List SourcedEntry
  /-- Which conjunction strategies are available (M&S classification). -/
  strategies : List ConjunctionStrategy
  /-- Structural patterns attested ([haspelmath-2007] classification). -/
  patterns : List CoordPattern := []
  /-- ISO 639-3 code. -/
  iso : String := ""
  deriving Repr

/-- A language's coordination typology profile across WALS Chs 56, 63, 64. -/
structure CoordinationProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Language family. -/
  family : String := ""
  /-- Ch 56: conjunction-vs-universal-quantifier. -/
  conjQuant : Option ConjQuantRelation := none
  /-- Ch 63: "and" vs "with". -/
  conjComitative : Option ConjComitativeRelation := none
  /-- Ch 64: NP-vs-VP conjunction. -/
  nomVerbalConj : Option NomVerbalConjRelation := none
  /-- Free-form provenance notes. -/
  walsNotes : String := ""
  deriving Repr

/-- Derive AND/WITH status for a coordination profile from its Ch 63 value. -/
def CoordinationProfile.andWithStatus (p : CoordinationProfile) :
    Option AndWithStatus :=
  p.conjComitative.map (·.toAndWithStatus)

/-! ### Helper predicates

The five `ConjunctionSystem.has*` predicates and `muIsAdditive` are
`Prop`-valued for clean theorem statements (no `= true` boilerplate).
Each has an explicit `Decidable` instance so concrete checks over finite
language samples close by `decide`. -/

/-- Does a language make a given conjunction strategy available? -/
def ConjunctionSystem.hasStrategy (sys : ConjunctionSystem)
    (s : ConjunctionStrategy) : Prop :=
  s ∈ sys.strategies

instance (sys : ConjunctionSystem) (s : ConjunctionStrategy) :
    Decidable (sys.hasStrategy s) := by
  unfold ConjunctionSystem.hasStrategy; infer_instance

/-- Does a language have a MU morpheme that also serves as the additive
    ("also/too") particle? Existential: at least one MU morpheme in the
    language's inventory has `alsoAdditive = true`. -/
def ConjunctionSystem.muIsAdditive (sys : ConjunctionSystem) : Prop :=
  ∃ m ∈ sys.morphemes, m.entry.role = .mu ∧ m.entry.alsoAdditive = true

instance (sys : ConjunctionSystem) : Decidable sys.muIsAdditive := by
  unfold ConjunctionSystem.muIsAdditive; infer_instance

/-- Does the language attest a morpheme with the given diachronic source? -/
def ConjunctionSystem.hasSource (sys : ConjunctionSystem)
    (s : DiachronicSource) : Prop :=
  ∃ m ∈ sys.morphemes, m.source = some s

instance (sys : ConjunctionSystem) (s : DiachronicSource) :
    Decidable (sys.hasSource s) := by
  unfold ConjunctionSystem.hasSource; infer_instance

/-- Does a language attest at least one monosyndetic pattern? -/
def ConjunctionSystem.hasMonosyndetic (sys : ConjunctionSystem) : Prop :=
  ∃ p ∈ sys.patterns, p.syndesis = .monosyndetic

instance (sys : ConjunctionSystem) : Decidable sys.hasMonosyndetic := by
  unfold ConjunctionSystem.hasMonosyndetic; infer_instance

/-- Does a language attest at least one bisyndetic pattern? -/
def ConjunctionSystem.hasBisyndetic (sys : ConjunctionSystem) : Prop :=
  ∃ p ∈ sys.patterns, p.syndesis = .bisyndetic

instance (sys : ConjunctionSystem) : Decidable sys.hasBisyndetic := by
  unfold ConjunctionSystem.hasBisyndetic; infer_instance

/-- The boundness of a language's MU particle, if it has one. -/
def ConjunctionSystem.muBoundness (sys : ConjunctionSystem) : Option Features.Boundness :=
  (sys.morphemes.find? fun m => m.entry.role == .mu).map (·.entry.boundness)

/-! ### Coordinate-structure symmetry -/

/-- Structural symmetry of a coordinate phrase (`&P`): whether one conjunct is
    structurally more prominent (c-commands the other) or the structure is flat /
    multidominant. The three groups of analyses for selection-violating coordination
    ([schwarzer-2026]) disagree on this parameter:
    - **Bottom-up accounts** assume `asymmetric`: the first conjunct c-commands the
      second, so only it must satisfy the selector's c-selectional requirements.
    - **Linear/temporal-closeness accounts** are compatible with either; their
      predictions derive from linear/temporal order, not structure.
    - **Symmetric accounts** ([neeleman-etal-2022], [przepiorkowski-2024]) posit flat or
      multidominance structures with no structural prominence. -/
inductive CoordSymmetry where
  /-- Flat or multidominance: no conjunct is structurally more prominent. -/
  | symmetric
  /-- Binary `&P`: the first conjunct c-commands the second. -/
  | asymmetric
  deriving DecidableEq, Repr, BEq

end Syntax.Coordination
