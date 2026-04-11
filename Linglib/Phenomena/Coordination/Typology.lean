import Linglib.Core.Coordination
import Linglib.Core.WALS.Features.F56A
import Linglib.Core.WALS.Features.F63A
import Linglib.Core.WALS.Features.F64A
import Linglib.Fragments.Georgian.Coordination
import Linglib.Fragments.Hungarian.Coordination
import Linglib.Fragments.Latin.Coordination
import Linglib.Fragments.Irish.Coordination
import Linglib.Fragments.Japanese.Coordination
import Linglib.Fragments.German.Coordination

/-!
# Cross-Linguistic Typology of Coordination

Three complementary typological perspectives on coordination:

## 1. Structural Typology

Classifies coordination by overt form:
- **Syndesis**: asyndetic (A B), monosyndetic (A co-B), bisyndetic (co-A co-B)
- **Coordinator position**: prepositive (co-A) vs postpositive (A-co)
- **Universal gap**: the pattern co-A B is unattested (@cite{haspelmath-2007}; sample: @cite{stassen-2000}, n=260)
- **Diachronic sources**: comitative ("with") -> monosyndetic J;
  additive focus particle ("also") -> bisyndetic MU

## 2. Semantic Decomposition (@cite{mitrovic-sauerland-2014}, @cite{mitrovic-sauerland-2016})

Classifies by underlying semantic structure:
- J (set intersection) + MU (subset/additive) + type-shifter
- Languages vary in which pieces are overtly realized

## 3. WALS Typological Features (Chapters 56, 63, 64)

Three WALS features capture cross-linguistic variation in coordination:

### Ch 56: Conjunctions and Universal Quantifiers (@cite{dryer-haspelmath-2013})
Whether a language's conjunction marker ("and") is formally similar to
its universal quantifier ("all/every"). Three values:
- **Formally different**: "and" and "all" are unrelated forms (40/116)
- **Formally similar, without interrogative**: "and"/"all" are similar
  but the interrogative ("what/who") is different (33/116)
- **Formally similar, with interrogative**: "and"/"all"/"wh" are all
  formally similar (43/116)

### Ch 63: Noun Phrase Conjunction (@cite{dryer-haspelmath-2013})
Whether a language's NP conjunction marker ("and") is the same as its
comitative marker ("with"). Two values:
- **'And' different from 'with'**: distinct forms (131/234)
- **'And' identical to 'with'**: same form for both (103/234)

### Ch 64: Nominal and Verbal Conjunction (@cite{dryer-haspelmath-2013})
Whether a language uses the same marker for NP conjunction ("A and B")
and VP/clausal conjunction ("sang and danced"). Three values:
- **Identity**: same marker for both (161/301)
- **Differentiation**: different markers (125/301)
- **Both expressed by juxtaposition**: no overt marker for either (15/301)

## Connection

Haspelmath's structural categories map onto M&S's semantic pieces:
- Monosyndetic medial (A co-B) = J-only (comitative source)
- Bisyndetic postpositive (A-co B-co) = MU-only (focus particle source)
- Bisyndetic mixed (co-A co-B, A-co co-B) = J-MU (both sources)

The MU particle in conjunction is typically the SAME morpheme as the
language's additive/focus particle, confirming the diachronic link.

The WALS Ch 63 feature (and = with) connects directly to the diachronic
comitative source: languages where "and" IS "with" are precisely those
where the comitative-to-coordinator grammaticalization is still transparent.
-/

namespace Phenomena.Coordination.Typology

open Core.Coordination

-- ============================================================================
-- @cite{haspelmath-2007}: Structural Typology
-- ============================================================================

/-- Syndesis: presence and number of overt coordinators (Haspelmath §1). -/
inductive Syndesis where
  | asyndetic      -- A B (juxtaposition, no overt linker)
  | monosyndetic   -- A co-B (single coordinator)
  | bisyndetic     -- co-A co-B (two coordinators, one per coordinand)
  deriving DecidableEq, Repr

/--
Coordinator position relative to its coordinand (Haspelmath §1.2).

@cite{haspelmath-2007} notes that **co-A B (prepositive on first coordinand only)
is unattested** (cf. @cite{stassen-2000}, n=260). This is the one
logically possible monosyndetic pattern that never occurs.
-/
inductive CoordinatorPosition where
  | prepositive    -- co precedes coordinand: "and A" / English "both X"
  | postpositive   -- co follows coordinand: "A-and" / Latin "X-que"
  deriving DecidableEq, Repr

/--
Structural pattern for binary coordination (Haspelmath (17)).

Monosyndetic: 3 attested patterns (of 4 logically possible).
  A co-B (prepositive on 2nd: English "A and B")
  A-co B (postpositive on 1st: Tibetan "A-daŋ B")
  A B-co (postpositive on 2nd: Latin "A B-que")

  co-A B — UNATTESTED (@cite{haspelmath-2007}; cf. @cite{stassen-2000}, n=260)

Bisyndetic: 4 attested patterns.
  co-A co-B (prepositive: Yoruba "àtí A àtí B")
  A-co B-co (postpositive: Martuthunira "A-thurti B-thurti")
  A-co co-B (mixed: Homeric Greek "A-te kaì B")
  co-A B-co (mixed: Latin "et A B-que")
-/
inductive CoordPattern where
  /-- A co-B: medial prepositive (English "A and B", Lango "A kèdè B") -/
  | a_co_b
  /-- A-co B: medial postpositive on 1st (Tibetan "A-daŋ B") -/
  | a'co_b
  /-- A B-co: final postpositive (Latin "senatus populus-que") -/
  | a_b'co
  /-- co-A co-B: prepositive bisyndetic (Yoruba "àtí A àtí B") -/
  | co'a_co'b
  /-- A-co B-co: postpositive bisyndetic (Martuthunira "A-thurti B-thurti") -/
  | a'co_b'co
  /-- A-co co-B: mixed bisyndetic (Homeric Greek "A-te kaì B") -/
  | a'co_co'b
  /-- co-A B-co: mixed bisyndetic (Latin "et A B-que") -/
  | co'a_b'co
  deriving DecidableEq, Repr

/-- Classify a pattern's syndesis. -/
def CoordPattern.syndesis : CoordPattern → Syndesis
  | .a_co_b | .a'co_b | .a_b'co => .monosyndetic
  | .co'a_co'b | .a'co_b'co | .a'co_co'b | .co'a_b'co => .bisyndetic

/--
Diachronic source of conjunction constructions (Haspelmath §5.1, p.10).

Two main pathways create conjunction markers:
1. Comitative "with" → monosyndetic coordinator (A with B → A and B)
2. Additive focus particle "also/too" → bisyndetic coordinator (A also B also)
-/
inductive DiachronicSource where
  | comitative      -- "with" → coordinator (gives A co-B or A-co B)
  | focusParticle   -- "also/too" → coordinator (gives A-co B-co)
  | other
  deriving DecidableEq, Repr

/--
Haspelmath's key insight connecting diachronic source to structural pattern:
- Comitative source → monosyndetic (because "with" links two NPs)
- Focus particle source → bisyndetic (because "also" marks each NP)

This aligns with M&S: J ≈ comitative-derived, MU ≈ focus-particle-derived.
-/
def DiachronicSource.expectedPattern : DiachronicSource → Syndesis
  | .comitative    => .monosyndetic
  | .focusParticle => .bisyndetic
  | .other         => .monosyndetic  -- default

-- ============================================================================
-- Language Data: Structures
-- ============================================================================

/-- A coordination entry annotated with its diachronic source.
    Wraps `CoordEntry` (from `Core.Coordination`) with typological metadata.
    For languages with Fragment files, `entry` references the Fragment entry
    directly — no data duplication. -/
structure SourcedEntry where
  /-- The coordination morpheme entry. -/
  entry : CoordEntry
  /-- Likely diachronic source, if known. -/
  source : Option DiachronicSource := none
  deriving Repr

/-- A language's conjunction system. -/
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

-- ============================================================================
-- Language Data: M&S Focus Languages
-- ============================================================================

/--
English only has J ("and"). "Both...and" is sometimes analyzed as J-MU,
but "both" is not productively used as an additive particle (*"John both
slept") and English lacks MU-only conjunction (*"John both Mary both slept").
See FormMeaning.lean `andBoth` for the "both" ≈ precision-adding analysis.
-/
def english : ConjunctionSystem :=
  { language := "English"
  , morphemes :=
    [ { entry := { form := "and", gloss := "and", role := .j, boundness := .free } } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "eng" }

/--
German uses "und" (J, free word), like English "and". J-only strategy.
German is the test language for @cite{schwarzer-2026}'s study of
selection-violating coordination in OV environments.
-/
def german : ConjunctionSystem :=
  { language := "German"
  , morphemes :=
    [ { entry := Fragments.German.Coordination.und } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "deu" }

/--
Japanese conjunction uses "to" (J) and "mo" (MU).
"to" derives from the comitative marker. "mo" is also the additive
particle (see AdditiveParticles/Data.lean `japaneseMo`).
-/
def japanese : ConjunctionSystem :=
  { language := "Japanese"
  , morphemes :=
    [ { entry := Fragments.Japanese.Coordination.to_
      , source := some .comitative }
    , { entry := Fragments.Japanese.Coordination.mo
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a'co_b, .a'co_b'co]
  , iso := "jpn" }

/--
Hungarian: "és" (J, free, prepositive), "is" (MU, free, postpositive).
"is" is also the additive focus particle ("also").
One of two languages in our sample with all three strategies (J, MU, J-MU).
-/
def hungarian : ConjunctionSystem :=
  { language := "Hungarian"
  , morphemes :=
    [ { entry := Fragments.Hungarian.Coordination.es }
    , { entry := Fragments.Hungarian.Coordination.is_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "hun" }

/--
Georgian: "da" (J, free), "-c" (MU, bound clitic).
"-c" is also the additive/focus particle.
One of two languages in our sample with all three strategies.
-/
def georgian : ConjunctionSystem :=
  { language := "Georgian"
  , morphemes :=
    [ { entry := Fragments.Georgian.Coordination.da }
    , { entry := Fragments.Georgian.Coordination.c_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "kat" }

/--
Latin: "et" (J, free, prepositive) and "-que" (MU, bound enclitic, postpositive).
"-que" is the classic bound MU particle. Three structural patterns attested:
A et B (monosyndetic), A B-que (monosyndetic), et A B-que (mixed bisyndetic).
-/
def latin : ConjunctionSystem :=
  { language := "Latin"
  , morphemes :=
    [ { entry := Fragments.Latin.Coordination.et }
    , { entry := Fragments.Latin.Coordination.que
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a_b'co, .co'a_b'co]
  , iso := "lat" }

/--
Korean: "-(i)rang" (J, bound, postpositive) and "-to" (MU, bound, also additive).
Pattern: A-(i)rang B (monosyndetic postpositive), A-to B-to (bisyndetic postpositive).
-/
def korean : ConjunctionSystem :=
  { language := "Korean"
  , morphemes :=
    [ { entry := { form := "-(i)rang", gloss := "and", role := .j, boundness := .bound } }
    , { entry := { form := "-to", gloss := "also, too; and (MU)"
                 , role := .mu, boundness := .bound, alsoAdditive := true }
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a'co_b, .a'co_b'co]
  , iso := "kor" }

/--
Slovenian: "in" (J, free, prepositive).
Primarily J-only for standard conjunction.
-/
def slovenian : ConjunctionSystem :=
  { language := "Slovenian"
  , morphemes :=
    [ { entry := { form := "in", gloss := "and", role := .j, boundness := .free } } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "slv" }

-- ============================================================================
-- Language Data: @cite{haspelmath-2007} Typological Examples
-- ============================================================================

/--
Lango (Nilotic, Uganda): "kèdè" is a comitative marker ("with") that also
serves as coordinator ("and"). The classic AND-language: comitative source
gives monosyndetic A co-B (@cite{noonan-1992}:163, @cite{haspelmath-2007}: (20)).
-/
def lango : ConjunctionSystem :=
  { language := "Lango"
  , morphemes :=
    [ { entry := { form := "kèdè", gloss := "and; with", role := .j, boundness := .free }
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "laj" }

/--
Hausa (Chadic, Nigeria): "da" means both "with" (comitative) and "and"
(conjunction). Archetypal comitative → conjunction path
(@cite{schwartz-1989}:32,36; @cite{haspelmath-2007}: (12)).
-/
def hausa : ConjunctionSystem :=
  { language := "Hausa"
  , morphemes :=
    [ { entry := { form := "da", gloss := "and; with", role := .j, boundness := .free }
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "hau" }

/--
Yoruba (Kwa, Nigeria): "àtí" in the pattern "àtí A àtí B" is the canonical
example of prepositive bisyndetic coordination
(@cite{rowlands-1969}:201ff, @cite{haspelmath-2007}: (25)).
-/
def yoruba : ConjunctionSystem :=
  { language := "Yoruba"
  , morphemes :=
    [ { entry := { form := "àtí", gloss := "and", role := .j, boundness := .free } } ]
  , strategies := [.jOnly]
  , patterns := [.co'a_co'b]
  , iso := "yor" }

/--
Kannada (Dravidian, southern India): postpositive "-u" on each coordinand
gives A-co B-co (@cite{sridhar-1990}:106, @cite{haspelmath-2007}: (5)).
"-u" is also the additive/focus particle in Dravidian.
-/
def kannada : ConjunctionSystem :=
  { language := "Kannada"
  , morphemes :=
    [ { entry := { form := "-u", gloss := "and; also", role := .mu, boundness := .bound
                 , alsoAdditive := true }
      , source := some .focusParticle } ]
  , strategies := [.muOnly]
  , patterns := [.a'co_b'co]
  , iso := "kan" }

/--
Martuthunira (Pama-Nyungan, W. Australia): "-thurti" on each coordinand
gives A-co B-co (@cite{dench-1995}:98, @cite{haspelmath-2007}: (26)).
-/
def martuthunira : ConjunctionSystem :=
  { language := "Martuthunira"
  , morphemes :=
    [ { entry := { form := "-thurti", gloss := "and", role := .j, boundness := .bound } } ]
  , strategies := [.jOnly]
  , patterns := [.a'co_b'co]
  , iso := "vma" }

/--
Classical Tibetan: "-daŋ" is postpositive on first coordinand, giving A-co B.
Derives from comitative source (@cite{beyer-1992}:240, @cite{haspelmath-2007}: (21)).
-/
def classicalTibetan : ConjunctionSystem :=
  { language := "Classical Tibetan"
  , morphemes :=
    [ { entry := { form := "-daŋ", gloss := "and; with", role := .j, boundness := .bound }
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a'co_b]
  , iso := "xct" }

/--
Hindi-Urdu: "aur" (J, free, prepositive) and "bhii" (MU, free, additive).
"bhii" is the additive particle "also/too" (see AdditiveParticles).
Pattern: A aur B (monosyndetic), A bhii B bhii (bisyndetic postpositive).
-/
def hindiUrdu : ConjunctionSystem :=
  { language := "Hindi-Urdu"
  , morphemes :=
    [ { entry := { form := "aur", gloss := "and", role := .j, boundness := .free } }
    , { entry := { form := "bhii", gloss := "also, too; and (MU)"
                 , role := .mu, boundness := .free, alsoAdditive := true }
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "hin" }

/--
Turkish: "ve" (J, free, prepositive) and "de/da" (MU, free, additive).
"de/da" is the additive particle "also" (vowel harmony alternation).
Pattern: A ve B (monosyndetic), A da B de (bisyndetic postpositive).
-/
def turkish : ConjunctionSystem :=
  { language := "Turkish"
  , morphemes :=
    [ { entry := { form := "ve", gloss := "and", role := .j, boundness := .free } }
    , { entry := { form := "de/da", gloss := "also; and (MU)"
                 , role := .mu, boundness := .free, alsoAdditive := true }
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "tur" }

/--
Irish: "agus" (J, free, prepositive). No MU strategy attested.
Pattern: A agus B (monosyndetic medial).
-/
def irish : ConjunctionSystem :=
  { language := "Irish"
  , morphemes :=
    [ { entry := Fragments.Irish.Coordination.agus } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "gle" }

/--
Persian: "va" (J, free, prepositive) and "ham" (MU, free, additive).
"ham" is the additive particle "also/too".
Pattern: A va B (monosyndetic), A ham B ham (bisyndetic postpositive).
-/
def persian : ConjunctionSystem :=
  { language := "Persian"
  , morphemes :=
    [ { entry := { form := "va", gloss := "and", role := .j, boundness := .free } }
    , { entry := { form := "ham", gloss := "also, too; and (MU)"
                 , role := .mu, boundness := .free, alsoAdditive := true }
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "fas" }

/--
Finnish: "ja" (J, free, prepositive) and "-kin" (MU, bound, additive).
"-kin" is the additive focus particle "also/too":
*koira-kin kissa-kin* 'dog-too cat-too' = 'both the dog and the cat'.
Standard conjunction: *koira ja kissa* 'dog and cat' (monosyndetic medial).
-/
def finnish : ConjunctionSystem :=
  { language := "Finnish"
  , morphemes :=
    [ { entry := { form := "ja", gloss := "and", role := .j, boundness := .free } }
    , { entry := { form := "-kin", gloss := "also, too; and (MU)"
                 , role := .mu, boundness := .bound, alsoAdditive := true }
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "fin" }

def allLanguages : List ConjunctionSystem :=
  [ english, german, japanese, hungarian, georgian, latin, korean, slovenian
  , lango, hausa, yoruba, kannada, martuthunira, classicalTibetan
  , hindiUrdu, turkish, irish, persian, finnish ]

-- ============================================================================
-- Typological Generalizations: M&S Semantic Decomposition
-- ============================================================================

/-- Does a language have a given strategy? -/
def ConjunctionSystem.hasStrategy (sys : ConjunctionSystem) (s : ConjunctionStrategy) : Bool :=
  sys.strategies.contains s

/-- Does a language have a MU morpheme that also serves as additive? -/
def ConjunctionSystem.muIsAdditive (sys : ConjunctionSystem) : Bool :=
  sys.morphemes.any fun m => m.entry.role == .mu && m.entry.alsoAdditive

/--
Every language with a MU conjunction particle uses the same morpheme
as its additive ("also/too") particle.

This is a core prediction of M&S / Mitrović (2021): MU is a single
lexical item with subset semantics that appears in both conjunction
and additive contexts.

NOTE: Restricted to languages in our sample that HAVE a MU morpheme.
-/
theorem mu_additive_generalization :
    let withMu := allLanguages.filter fun sys =>
      sys.morphemes.any (·.entry.role == .mu)
    withMu.all (·.muIsAdditive) = true := by
  native_decide

/--
All three strategies (J, MU, J-MU) attested only in Georgian and Hungarian
in our sample. This is typologically rare.
-/
def hasAllThreeStrategies (sys : ConjunctionSystem) : Bool :=
  sys.hasStrategy .jOnly && sys.hasStrategy .muOnly && sys.hasStrategy .jMu

theorem all_three_is_rare :
    let count := (allLanguages.filter hasAllThreeStrategies).length
    count == 2 := by
  native_decide

/-- Languages with full M&S strategy classification (from @cite{bill-etal-2025}). -/
def msLanguages : List ConjunctionSystem :=
  [english, japanese, hungarian, georgian, latin, korean, slovenian]

/-- Every M&S-classified language in our sample has at least the J-only strategy. -/
theorem j_is_universal :
    msLanguages.all (·.hasStrategy .jOnly) = true := by
  native_decide

-- ============================================================================
-- MU Boundness and the Georgian-Hungarian Asymmetry
-- ============================================================================

/-- Get the boundness of a language's MU particle, if it has one. -/
def ConjunctionSystem.muBoundness (sys : ConjunctionSystem) : Option Boundness :=
  (sys.morphemes.find? fun m => m.entry.role == .mu).map (·.entry.boundness)

/--
Georgian MU is bound, Hungarian MU is free.

@cite{bill-etal-2025} @cite{mitrovic-2021} speculate this morphological difference may explain
why Georgian children found MU-involving expressions harder than
Hungarian children did: bound morphemes are harder to segment and acquire.
-/
theorem mu_boundness_asymmetry :
    georgian.muBoundness = some .bound ∧
    hungarian.muBoundness = some .free := by
  native_decide

-- ============================================================================
-- Typological Generalizations: Haspelmath Structural Typology
-- ============================================================================

/-- Does a language have a morpheme with a given diachronic source? -/
def ConjunctionSystem.hasSource (sys : ConjunctionSystem) (s : DiachronicSource) : Bool :=
  sys.morphemes.any fun m => m.source == some s

/-- Does a language have at least one monosyndetic pattern? -/
def ConjunctionSystem.hasMonosyndetic (sys : ConjunctionSystem) : Bool :=
  sys.patterns.any fun p => p.syndesis == .monosyndetic

/-- Does a language have at least one bisyndetic pattern? -/
def ConjunctionSystem.hasBisyndetic (sys : ConjunctionSystem) : Bool :=
  sys.patterns.any fun p => p.syndesis == .bisyndetic

/--
Haspelmath's diachronic generalization (§5.1):
Every language with a known comitative-sourced morpheme has at least one
monosyndetic structural pattern.

This confirms: comitative "with" → monosyndetic A co-B / A-co B.
Languages: Lango ("kèdè"), Hausa ("da"), Japanese ("to"), Classical Tibetan ("-daŋ").
-/
theorem comitative_source_monosyndetic :
    let withComitative := allLanguages.filter (·.hasSource .comitative)
    withComitative.all (·.hasMonosyndetic) = true := by
  native_decide

/--
Haspelmath's diachronic generalization (§5.1):
Every language with a known focus-particle-sourced morpheme has at least
one bisyndetic structural pattern.

This confirms: additive focus particle "also" → bisyndetic A-co B-co.
Languages: Japanese ("mo"), Hungarian ("is"), Georgian ("-c"), Latin ("-que"),
Korean ("-to"), Kannada ("-u").
-/
theorem focus_particle_source_bisyndetic :
    let withFocusParticle := allLanguages.filter (·.hasSource .focusParticle)
    withFocusParticle.all (·.hasBisyndetic) = true := by
  native_decide

-- ============================================================================
-- The M&S Universality Claim (and its empirical challenge)
-- ============================================================================

/-!
## Mitrović & Sauerland's Universal Structure
@cite{stassen-2000} @cite{haspelmath-2007} @cite{schwartz-1989}

@cite{mitrovic-sauerland-2016} claim that EVERY language has the same underlying structure
for DP conjunction:

  [JP [MuP [DP ☉] MU] [J' J [MuP [DP ☉] MU]]]

All three strategies (J, MU, J-MU) are underlyingly identical.
What varies is which functional heads (J, MU₁, MU₂) are pronounced.

### Semantic content (via Montague/Conjunction.lean)

- ☉ = `msShift` (individual → singleton set, = Partee's `ident`)
- MU = `typeRaise` (INCL on singletons IS type-raising; structural `abbrev`)
- J = `genConj` at GQ type (Partee & Rooth set intersection)

`coordEntities` is defined AS `genConj(typeRaise e₁, typeRaise e₂)`,
so the M&S derivation is the definition itself.
`mu_is_distributive_check` (BillEtAl2025.lean) proves this equals
Link's `distMaximal` on pairs — the cross-theory unification.

The empirical challenge from @cite{bill-etal-2025} — Georgian children found J-MU
*harder*, not easier, contradicting the Transparency Principle prediction —
is formalized in `ms_universality_challenged` and `boundness_confound`
in `Studies/BillEtAl2025.lean`.
-/

-- ============================================================================
-- WALS Coordination Features (Chapters 56, 63, 64)
-- ============================================================================

-- ============================================================================
-- Chapter 56: Conjunctions and Universal Quantifiers
-- ============================================================================

/-- Short alias for WALS Ch 56 type. -/
abbrev ConjQuantRelation := Core.WALS.F56A.ConjunctionsAndUniversalQuantifiers

-- ============================================================================
-- Chapter 63: Noun Phrase Conjunction
-- ============================================================================

/-- Short alias for WALS Ch 63 type. -/
abbrev ConjComitativeRelation := Core.WALS.F63A.NounPhraseConjunction

/--
@cite{stassen-2000} AND/WITH classification of languages.
AND-languages have structurally distinct coordinate and comitative strategies.
WITH-languages use comitative encoding as the only strategy for NP conjunction.

Derived from WALS Ch 63 conjunction/comitative relation: languages where
"and" ≠ "with" have differentiated the two strategies (AND-status);
languages where "and" = "with" retain comitative-based conjunction (WITH-status).
-/
inductive AndWithStatus where
  | andLang   -- Coordinate and comitative are structurally distinct
  | withLang  -- Comitative marker = coordinator; no balanced coordination
  deriving DecidableEq, Repr

/-- Derive AND/WITH status from the conjunction-comitative relation.
    @cite{stassen-2000}: lexical identity of "and" and "with" is the
    diagnostic for WITH-language status. -/
def ConjComitativeRelation.toAndWithStatus : ConjComitativeRelation → AndWithStatus
  | .andDifferentFromWith => .andLang
  | .andIdenticalToWith   => .withLang

-- ============================================================================
-- Chapter 64: Nominal and Verbal Conjunction
-- ============================================================================

/-- Short alias for WALS Ch 64 type. -/
abbrev NomVerbalConjRelation := Core.WALS.F64A.NominalAndVerbalConjunction

-- ============================================================================
-- Coordination Profile Structure
-- ============================================================================

/-- A language's coordination typology profile across WALS Chapters 56, 63, 64. -/
structure CoordinationProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Language family. -/
  family : String := ""
  /-- Ch 56: Relationship between conjunction and universal quantifier. -/
  conjQuant : Option ConjQuantRelation := none
  /-- Ch 63: Whether "and" = "with". -/
  conjComitative : Option ConjComitativeRelation := none
  /-- Ch 64: Whether NP and VP conjunction use the same marker. -/
  nomVerbalConj : Option NomVerbalConjRelation := none
  /-- Notes on the coordination system. -/
  walsNotes : String := ""
  deriving Repr

/-- Derive AND/WITH status for a coordination profile from its Ch 63 value.
    @cite{stassen-2000}: lexical identity of "and" and "with" is the
    diagnostic for WITH-language status. -/
def CoordinationProfile.andWithStatus (p : CoordinationProfile) : Option AndWithStatus :=
  p.conjComitative.map (·.toAndWithStatus)

-- ============================================================================
-- Language Profiles
-- ============================================================================

/--
English (Indo-European, Germanic).
Ch 56: "and" and "every/all" are formally similar without interrogative link.
Ch 63: "and" is different from "with".
Ch 64: Same "and" for NP and VP coordination (identity).
-/
def englishWALS : CoordinationProfile :=
  { language := "English"
  , iso := "eng"
  , family := "Indo-European"
  , conjQuant := some .formallySimilarWithoutInterrogative
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'and' for both NP and VP coordination; " ++
                 "'and' differs from comitative 'with'" }

/--
German (Indo-European, Germanic).
Ch 56: Not in WALS F56A sample.
Ch 63: Not in WALS F63A sample.
Ch 64: Same "und" for NP and VP coordination (identity).
-/
def germanWALS : CoordinationProfile :=
  { language := "German"
  , iso := "deu"
  , family := "Indo-European"
  , conjQuant := none
  , conjComitative := none
  , nomVerbalConj := some .identity
  , walsNotes := "'und' for both NP and VP coordination; " ++
                 "absent from F56A and F63A WALS samples" }

/--
French (Indo-European, Romance).
Ch 56: "et" (and) and "tout/chaque" (all/every) are formally different.
Ch 63: "et" (and) is different from "avec" (with).
Ch 64: Same "et" for NP and VP coordination (identity).
-/
def frenchWALS : CoordinationProfile :=
  { language := "French"
  , iso := "fra"
  , family := "Indo-European"
  , conjQuant := some .formallyDifferent
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'et' for both NP and VP; formally distinct from " ++
                 "'avec' (with) and 'tout/chaque' (all/every)" }

/--
Spanish (Indo-European, Romance).
Ch 56: Not in WALS F56A sample.
Ch 63: "y" (and) is different from "con" (with).
Ch 64: Same "y" for NP and VP coordination (identity).
-/
def spanishWALS : CoordinationProfile :=
  { language := "Spanish"
  , iso := "spa"
  , family := "Indo-European"
  , conjQuant := none
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'y' for both NP and VP; distinct from 'con' (with); " ++
                 "absent from F56A WALS sample" }

/--
Russian (Indo-European, Slavic).
Ch 56: Not in WALS F56A sample.
Ch 63: "i" (and) is different from "s" (with).
Ch 64: Same "i" for NP and VP coordination (identity).
-/
def russianWALS : CoordinationProfile :=
  { language := "Russian"
  , iso := "rus"
  , family := "Indo-European"
  , conjQuant := none
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'i' for both NP and VP coordination; distinct from " ++
                 "'s' (with); absent from F56A WALS sample" }

/--
Japanese (Japonic).
Ch 56: Conjunction "mo", universal quantifier "mo" (dare-mo = everyone),
  and interrogative "dare" (who) are all formally similar.
Ch 63: "to" (and) is identical to "to" (with/comitative).
Ch 64: NP and VP conjunction use different strategies (differentiation).
  NP: "A to B" or "A mo B mo"; VP: different connective strategies.
-/
def japaneseWALS : CoordinationProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , family := "Japonic"
  , conjQuant := some .formallySimilarWithInterrogative
  , conjComitative := some .andIdenticalToWith
  , nomVerbalConj := some .differentiation
  , walsNotes := "'mo' links conjunction, universal quantifier, and " ++
                 "interrogative; 'to' serves as both and/with; " ++
                 "NP vs VP conjunction use different strategies" }

/--
Mandarin Chinese (Sino-Tibetan).
Ch 56: Conjunction, quantifier, and interrogative are formally similar.
Ch 63: "he" or "gen" (and) is identical to comitative "gen/he" (with).
Ch 64: NP and VP conjunction use different strategies (differentiation).
  NP: "A he B"; VP: different connective or serial verb.
-/
def mandarinWALS : CoordinationProfile :=
  { language := "Mandarin"
  , iso := "cmn"
  , family := "Sino-Tibetan"
  , conjQuant := some .formallySimilarWithInterrogative
  , conjComitative := some .andIdenticalToWith
  , nomVerbalConj := some .differentiation
  , walsNotes := "NP conjunction 'he/gen' doubles as comitative; " ++
                 "VP coordination uses different strategies; " ++
                 "conjunction-quantifier-interrogative formally linked" }

/--
Korean (Koreanic).
Ch 56: Not in WALS F56A sample.
Ch 63: Conjunction marker is different from comitative.
Ch 64: NP and VP conjunction use different markers (differentiation).
-/
def koreanWALS : CoordinationProfile :=
  { language := "Korean"
  , iso := "kor"
  , family := "Koreanic"
  , conjQuant := none
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .differentiation
  , walsNotes := "NP conjunction '-(i)rang, -(g)wa' differs from " ++
                 "comitative; VP uses different connective strategies; " ++
                 "absent from F56A WALS sample" }

/--
Turkish (Turkic).
Ch 56: "ve" (and) and "her" (every) are formally different.
Ch 63: "ve" (and) is different from "ile" (with).
Ch 64: Same conjunction for NP and VP coordination (identity).
-/
def turkishWALS : CoordinationProfile :=
  { language := "Turkish"
  , iso := "tur"
  , family := "Turkic"
  , conjQuant := some .formallyDifferent
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'ve' for both NP and VP coordination; formally " ++
                 "distinct from 'ile' (with) and 'her' (every)" }

/--
Finnish (Uralic).
Ch 56: Conjunction and universal quantifier formally similar with
  interrogative link.
Ch 63: "ja" (and) is different from comitative case marker.
Ch 64: Same "ja" for NP and VP coordination (identity).
-/
def finnishWALS : CoordinationProfile :=
  { language := "Finnish"
  , iso := "fin"
  , family := "Uralic"
  , conjQuant := some .formallySimilarWithInterrogative
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'ja' for both NP and VP; comitative expressed by " ++
                 "case suffix, not 'ja'; conjunction-quantifier-" ++
                 "interrogative formally linked" }

/--
Hungarian (Uralic).
Ch 56: Conjunction and universal quantifier formally similar without
  interrogative link.
Ch 63: "és" (and) is different from comitative "-val, -vel" (with).
Ch 64: Same "és" for NP and VP coordination (identity).
-/
def hungarianWALS : CoordinationProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , family := "Uralic"
  , conjQuant := some .formallySimilarWithoutInterrogative
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'és' for both NP and VP; distinct from comitative " ++
                 "case suffix '-val, -vel'; conjunction and quantifier " ++
                 "formally similar but interrogative is different" }

/--
Hindi (Indo-European, Indo-Aryan).
Ch 56: Conjunction, universal quantifier, and interrogative formally similar.
Ch 63: "aur" (and) is different from "ke saath" (with).
Ch 64: Same "aur" for NP and VP coordination (identity).
-/
def hindiWALS : CoordinationProfile :=
  { language := "Hindi"
  , iso := "hin"
  , family := "Indo-European"
  , conjQuant := some .formallySimilarWithInterrogative
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'aur' for both NP and VP coordination; distinct from " ++
                 "comitative 'ke saath'; conjunction-quantifier-" ++
                 "interrogative formally linked" }

/--
Arabic (Egyptian) (Afro-Asiatic, Semitic).
Ch 56: Not in WALS F56A sample.
Ch 63: "wa/wi" (and) is different from "ma'a" (with).
Ch 64: Same conjunction for NP and VP coordination (identity).
-/
def arabicWALS : CoordinationProfile :=
  { language := "Arabic (Egyptian)"
  , iso := "arz"
  , family := "Afro-Asiatic"
  , conjQuant := none
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'wa/wi' for both NP and VP coordination; distinct " ++
                 "from comitative 'ma'a'; absent from F56A WALS sample" }

/--
Swahili (Niger-Congo, Bantu).
Ch 56: Not in WALS F56A sample.
Ch 63: "na" serves as both conjunction ("and") and comitative ("with").
Ch 64: Not in WALS F64A sample.
-/
def swahiliWALS : CoordinationProfile :=
  { language := "Swahili"
  , iso := "swh"
  , family := "Niger-Congo"
  , conjQuant := none
  , conjComitative := some .andIdenticalToWith
  , nomVerbalConj := none
  , walsNotes := "'na' serves as both 'and' and 'with'; classic " ++
                 "comitative=conjunction pattern; absent from F56A " ++
                 "and F64A WALS samples" }

/--
Tagalog (Austronesian).
Ch 56: Conjunction, universal quantifier, and interrogative formally similar.
Ch 63: "at" (and) is different from "kasama" (with).
Ch 64: Same conjunction for NP and VP coordination (identity).
-/
def tagalogWALS : CoordinationProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , family := "Austronesian"
  , conjQuant := some .formallySimilarWithInterrogative
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'at' for both NP and VP coordination; distinct from " ++
                 "comitative; conjunction-quantifier-interrogative " ++
                 "formally linked" }

/-- All WALS coordination profiles in the sample. -/
def allWALSProfiles : List CoordinationProfile :=
  [ englishWALS, germanWALS, frenchWALS, spanishWALS, russianWALS
  , japaneseWALS, mandarinWALS, koreanWALS, turkishWALS, finnishWALS
  , hungarianWALS, hindiWALS, arabicWALS, swahiliWALS, tagalogWALS ]

-- ============================================================================
-- WALS Data Abbreviations
-- ============================================================================

private abbrev ch56 := Core.WALS.F56A.allData
private abbrev ch63 := Core.WALS.F63A.allData
private abbrev ch64 := Core.WALS.F64A.allData

-- ============================================================================
-- Per-Language WALS Grounding Theorems
-- ============================================================================

-- F56A grounding (9 languages present)
theorem english_f56a :
    (Core.WALS.F56A.lookup "eng").map (·.value) =
    englishWALS.conjQuant := by native_decide
theorem french_f56a :
    (Core.WALS.F56A.lookup "fre").map (·.value) =
    frenchWALS.conjQuant := by native_decide
theorem japanese_f56a :
    (Core.WALS.F56A.lookup "jpn").map (·.value) =
    japaneseWALS.conjQuant := by native_decide
theorem mandarin_f56a :
    (Core.WALS.F56A.lookup "mnd").map (·.value) =
    mandarinWALS.conjQuant := by native_decide
theorem turkish_f56a :
    (Core.WALS.F56A.lookup "tur").map (·.value) =
    turkishWALS.conjQuant := by native_decide
theorem finnish_f56a :
    (Core.WALS.F56A.lookup "fin").map (·.value) =
    finnishWALS.conjQuant := by native_decide
theorem hungarian_f56a :
    (Core.WALS.F56A.lookup "hun").map (·.value) =
    hungarianWALS.conjQuant := by native_decide
theorem hindi_f56a :
    (Core.WALS.F56A.lookup "hin").map (·.value) =
    hindiWALS.conjQuant := by native_decide
theorem tagalog_f56a :
    (Core.WALS.F56A.lookup "tag").map (·.value) =
    tagalogWALS.conjQuant := by native_decide

-- F63A grounding (14 languages present; German absent)
theorem english_f63a :
    (Core.WALS.F63A.lookup "eng").map (·.value) =
    englishWALS.conjComitative := by native_decide
theorem french_f63a :
    (Core.WALS.F63A.lookup "fre").map (·.value) =
    frenchWALS.conjComitative := by native_decide
theorem spanish_f63a :
    (Core.WALS.F63A.lookup "spa").map (·.value) =
    spanishWALS.conjComitative := by native_decide
theorem russian_f63a :
    (Core.WALS.F63A.lookup "rus").map (·.value) =
    russianWALS.conjComitative := by native_decide
theorem japanese_f63a :
    (Core.WALS.F63A.lookup "jpn").map (·.value) =
    japaneseWALS.conjComitative := by native_decide
theorem mandarin_f63a :
    (Core.WALS.F63A.lookup "mnd").map (·.value) =
    mandarinWALS.conjComitative := by native_decide
theorem korean_f63a :
    (Core.WALS.F63A.lookup "kor").map (·.value) =
    koreanWALS.conjComitative := by native_decide
theorem turkish_f63a :
    (Core.WALS.F63A.lookup "tur").map (·.value) =
    turkishWALS.conjComitative := by native_decide
theorem finnish_f63a :
    (Core.WALS.F63A.lookup "fin").map (·.value) =
    finnishWALS.conjComitative := by native_decide
theorem hungarian_f63a :
    (Core.WALS.F63A.lookup "hun").map (·.value) =
    hungarianWALS.conjComitative := by native_decide
theorem hindi_f63a :
    (Core.WALS.F63A.lookup "hin").map (·.value) =
    hindiWALS.conjComitative := by native_decide
theorem arabic_f63a :
    (Core.WALS.F63A.lookup "aeg").map (·.value) =
    arabicWALS.conjComitative := by native_decide
theorem swahili_f63a :
    (Core.WALS.F63A.lookup "swa").map (·.value) =
    swahiliWALS.conjComitative := by native_decide
theorem tagalog_f63a :
    (Core.WALS.F63A.lookup "tag").map (·.value) =
    tagalogWALS.conjComitative := by native_decide

-- F64A grounding (14 languages present; Swahili absent)
theorem english_f64a :
    (Core.WALS.F64A.lookup "eng").map (·.value) =
    englishWALS.nomVerbalConj := by native_decide
theorem german_f64a :
    (Core.WALS.F64A.lookup "ger").map (·.value) =
    germanWALS.nomVerbalConj := by native_decide
theorem french_f64a :
    (Core.WALS.F64A.lookup "fre").map (·.value) =
    frenchWALS.nomVerbalConj := by native_decide
theorem spanish_f64a :
    (Core.WALS.F64A.lookup "spa").map (·.value) =
    spanishWALS.nomVerbalConj := by native_decide
theorem russian_f64a :
    (Core.WALS.F64A.lookup "rus").map (·.value) =
    russianWALS.nomVerbalConj := by native_decide
theorem japanese_f64a :
    (Core.WALS.F64A.lookup "jpn").map (·.value) =
    japaneseWALS.nomVerbalConj := by native_decide
theorem mandarin_f64a :
    (Core.WALS.F64A.lookup "mnd").map (·.value) =
    mandarinWALS.nomVerbalConj := by native_decide
theorem korean_f64a :
    (Core.WALS.F64A.lookup "kor").map (·.value) =
    koreanWALS.nomVerbalConj := by native_decide
theorem turkish_f64a :
    (Core.WALS.F64A.lookup "tur").map (·.value) =
    turkishWALS.nomVerbalConj := by native_decide
theorem finnish_f64a :
    (Core.WALS.F64A.lookup "fin").map (·.value) =
    finnishWALS.nomVerbalConj := by native_decide
theorem hungarian_f64a :
    (Core.WALS.F64A.lookup "hun").map (·.value) =
    hungarianWALS.nomVerbalConj := by native_decide
theorem hindi_f64a :
    (Core.WALS.F64A.lookup "hin").map (·.value) =
    hindiWALS.nomVerbalConj := by native_decide
theorem arabic_f64a :
    (Core.WALS.F64A.lookup "aeg").map (·.value) =
    arabicWALS.nomVerbalConj := by native_decide
theorem tagalog_f64a :
    (Core.WALS.F64A.lookup "tag").map (·.value) =
    tagalogWALS.nomVerbalConj := by native_decide

-- ============================================================================
-- WALS Distribution Count Theorems
-- ============================================================================

/-- F56A total: 116 languages. -/
theorem wals_f56a_total : ch56.length = 116 := by native_decide

/-- F56A distribution: conjunctions and universal quantifiers. -/
theorem wals_f56a_formallyDifferent :
    (ch56.filter (·.value == .formallyDifferent)).length = 40 := by native_decide
theorem wals_f56a_similarNoInterrogative :
    (ch56.filter (·.value == .formallySimilarWithoutInterrogative)).length = 33 := by native_decide
theorem wals_f56a_similarWithInterrogative :
    (ch56.filter (·.value == .formallySimilarWithInterrogative)).length = 43 := by native_decide

/-- F63A total: 234 languages. -/
theorem wals_f63a_total : ch63.length = 234 := by native_decide

/-- F63A distribution: noun phrase conjunction. -/
theorem wals_f63a_andDifferentFromWith :
    (ch63.filter (·.value == .andDifferentFromWith)).length = 131 := by native_decide
theorem wals_f63a_andIdenticalToWith :
    (ch63.filter (·.value == .andIdenticalToWith)).length = 103 := by native_decide

/-- F64A total: 301 languages. -/
theorem wals_f64a_total : ch64.length = 301 := by native_decide

/-- F64A distribution: nominal and verbal conjunction. -/
theorem wals_f64a_identity :
    (ch64.filter (·.value == .identity)).length = 161 := by native_decide
theorem wals_f64a_differentiation :
    (ch64.filter (·.value == .differentiation)).length = 125 := by native_decide
theorem wals_f64a_juxtaposition :
    (ch64.filter (·.value == .bothExpressedByJuxtaposition)).length = 15 := by native_decide

-- ============================================================================
-- WALS Profile Sample Statistics
-- ============================================================================

/-- Number of WALS coordination profiles in our sample. -/
theorem wals_profile_count : allWALSProfiles.length = 15 := by native_decide

-- ============================================================================
-- WALS Typological Generalizations
-- ============================================================================

/-- F63A: "and" being different from "with" is the majority pattern (131 > 103). -/
theorem and_with_different_is_majority : (131 : Nat) > 103 := by native_decide

/-- F64A: Identity of NP and VP conjunction is the majority pattern (161/301). -/
theorem nom_verbal_identity_is_majority : (161 : Nat) > 125 ∧ (161 : Nat) > 15 := by
  exact ⟨by native_decide, by native_decide⟩

/-- F56A: Formal similarity between conjunction and universal quantifier
    (with or without interrogative) is the majority pattern: 33 + 43 = 76 > 40. -/
theorem conj_quant_similarity_majority : (33 : Nat) + 43 > 40 := by native_decide

/-- F64A: Juxtaposition for both NP and VP conjunction is rare (15/301 = 5%). -/
theorem juxtaposition_rare : (15 : Nat) * 20 < 301 := by native_decide

/-- F63A connects to diachronic source: languages where "and" = "with"
    (103/234 = 44%) are those with transparent comitative-to-coordinator
    grammaticalization. This is a substantial minority but not the majority. -/
theorem comitative_source_substantial_minority :
    (103 : Nat) * 2 < 234 ∧ (103 : Nat) * 3 > 234 := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- AND/WITH Classification (@cite{stassen-2000})
-- ============================================================================

/-- In the WALS F63A sample, AND-languages outnumber WITH-languages (131 > 103).
    @cite{stassen-2000}: this reflects the diachronic drift from WITH → AND. -/
theorem and_languages_majority :
    (ch63.filter (·.value == .andDifferentFromWith)).length >
    (ch63.filter (·.value == .andIdenticalToWith)).length := by native_decide

/-- Per-language AND/WITH classification. -/
theorem english_is_andLang : englishWALS.andWithStatus = some .andLang := by native_decide
theorem french_is_andLang : frenchWALS.andWithStatus = some .andLang := by native_decide
theorem spanish_is_andLang : spanishWALS.andWithStatus = some .andLang := by native_decide
theorem russian_is_andLang : russianWALS.andWithStatus = some .andLang := by native_decide
theorem japanese_is_withLang : japaneseWALS.andWithStatus = some .withLang := by native_decide
theorem mandarin_is_withLang : mandarinWALS.andWithStatus = some .withLang := by native_decide
theorem korean_is_andLang : koreanWALS.andWithStatus = some .andLang := by native_decide
theorem turkish_is_andLang : turkishWALS.andWithStatus = some .andLang := by native_decide
theorem finnish_is_andLang : finnishWALS.andWithStatus = some .andLang := by native_decide
theorem hungarian_is_andLang : hungarianWALS.andWithStatus = some .andLang := by native_decide
theorem hindi_is_andLang : hindiWALS.andWithStatus = some .andLang := by native_decide
theorem arabic_is_andLang : arabicWALS.andWithStatus = some .andLang := by native_decide
theorem swahili_is_withLang : swahiliWALS.andWithStatus = some .withLang := by native_decide
theorem tagalog_is_andLang : tagalogWALS.andWithStatus = some .andLang := by native_decide

end Phenomena.Coordination.Typology
