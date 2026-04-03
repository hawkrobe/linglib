import Linglib.Phenomena.Coordination.Studies.BillEtAl2025
import Linglib.Core.WALS.Features.F56A
import Linglib.Core.WALS.Features.F63A
import Linglib.Core.WALS.Features.F64A

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

open Phenomena.Coordination.Studies.BillEtAl2025

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

/--
Morphological boundness: whether a particle is a clitic/suffix or a free word.
Relevant to acquisition (@cite{clark-2017}: free morphemes acquired more readily).
-/
inductive Boundness where
  | free    -- independent word (Hungarian "is", English "and")
  | bound   -- clitic or suffix (Georgian "-c", Latin "-que")
  deriving DecidableEq, Repr

/-- A conjunction morpheme in a specific language. -/
structure ConjMorpheme where
  form : String
  role : String         -- "J" or "MU"
  boundness : Boundness
  /-- Does this morpheme also serve as an additive/focus particle? -/
  alsoAdditive : Bool
  /-- Likely diachronic source, if known -/
  source : Option DiachronicSource := none
  deriving Repr

/-- A language's conjunction system. -/
structure ConjunctionSystem where
  language : String
  /-- Available conjunction morphemes -/
  morphemes : List ConjMorpheme
  /-- Which conjunction strategies are available (M&S classification) -/
  strategies : List ConjunctionStrategy
  /-- Structural patterns attested (Haspelmath classification) -/
  patterns : List CoordPattern := []
  /-- ISO 639-3 code -/
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
    [ { form := "and", role := "J", boundness := .free, alsoAdditive := false } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "eng" }

/--
Japanese conjunction uses "to" (J) and "mo" (MU).
"to" derives from the comitative marker. "mo" is also the additive
particle (see AdditiveParticles/Data.lean `japaneseMo`).
-/
def japanese : ConjunctionSystem :=
  { language := "Japanese"
  , morphemes :=
    [ { form := "to", role := "J", boundness := .bound, alsoAdditive := false
      , source := some .comitative }
    , { form := "mo", role := "MU", boundness := .bound, alsoAdditive := true
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
    [ { form := "és", role := "J", boundness := .free, alsoAdditive := false }
    , { form := "is", role := "MU", boundness := .free, alsoAdditive := true
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
    [ { form := "da", role := "J", boundness := .free, alsoAdditive := false }
    , { form := "-c", role := "MU", boundness := .bound, alsoAdditive := true
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
    [ { form := "et", role := "J", boundness := .free, alsoAdditive := false }
    , { form := "-que", role := "MU", boundness := .bound, alsoAdditive := true
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
    [ { form := "-(i)rang", role := "J", boundness := .bound, alsoAdditive := false }
    , { form := "-to", role := "MU", boundness := .bound, alsoAdditive := true
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
    [ { form := "in", role := "J", boundness := .free, alsoAdditive := false } ]
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
    [ { form := "kèdè", role := "J", boundness := .free, alsoAdditive := false
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
    [ { form := "da", role := "J", boundness := .free, alsoAdditive := false
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
    [ { form := "àtí", role := "J", boundness := .free, alsoAdditive := false } ]
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
    [ { form := "-u", role := "MU", boundness := .bound, alsoAdditive := true
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
    [ { form := "-thurti", role := "J", boundness := .bound, alsoAdditive := false } ]
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
    [ { form := "-daŋ", role := "J", boundness := .bound, alsoAdditive := false
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
    [ { form := "aur", role := "J", boundness := .free, alsoAdditive := false }
    , { form := "bhii", role := "MU", boundness := .free, alsoAdditive := true
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
    [ { form := "ve", role := "J", boundness := .free, alsoAdditive := false }
    , { form := "de/da", role := "MU", boundness := .free, alsoAdditive := true
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
    [ { form := "agus", role := "J", boundness := .free, alsoAdditive := false } ]
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
    [ { form := "va", role := "J", boundness := .free, alsoAdditive := false }
    , { form := "ham", role := "MU", boundness := .free, alsoAdditive := true
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
    [ { form := "ja", role := "J", boundness := .free, alsoAdditive := false }
    , { form := "-kin", role := "MU", boundness := .bound, alsoAdditive := true
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "fin" }

def allLanguages : List ConjunctionSystem :=
  [ english, japanese, hungarian, georgian, latin, korean, slovenian
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
  sys.morphemes.any fun m => m.role == "MU" && m.alsoAdditive

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
      sys.morphemes.any (·.role == "MU")
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
  (sys.morphemes.find? fun m => m.role == "MU").map (·.boundness)

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

- J = `genConj` at type ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩ (Partee & Rooth set intersection)
- MU = `inclFunc` (INCL schema: subset check)
- ☉ = `typeRaise` (individual → generalized quantifier)

See `BillEtAl2025.ms_decomposition_eq_coord` for the proof that this
roundtrip recovers standard `coordEntities` semantics.
-/

/--
**Empirical challenge to M&S universality.**

The M&S decomposition + Transparency Principle predicts J-MU (where all
semantic pieces are overtly realized) should be EASIEST to acquire. But in
Georgian, J-MU is significantly HARDER for children than either J-only
or MU-only.

This theorem surfaces the contradiction at the typology level so that
any module importing Typology.lean sees that the M&S categories are
empirically contested, not established universals.

Conjunct 1: Georgian has all three M&S strategies (as M&S predicts).
Conjunct 2: M&S + Transparency predicts J-MU is most transparent.
Conjunct 3: Georgian children found J-MU significantly harder (more replays).
-/
theorem ms_universality_challenged :
    hasAllThreeStrategies georgian = true ∧
    transparencyPredicts .jMu .jOnly = true ∧
    georgianChild_j_vs_jmu.significant = true ∧
    georgianChild_j_vs_jmu.estimate_thou < 0 := by
  native_decide

/--
**The boundness confound.**

Georgian MU (-c) is bound; Hungarian MU (is) is free. Hungarian children
showed no significant sentence-type effect on either accuracy or replays.
This raises the possibility that morphological boundness — not the M&S
decomposition itself — drives the Georgian difficulty.

If boundness is the real factor, then M&S categories (J, MU, J-MU) are
not the right level of analysis for acquisition predictions.
-/
theorem boundness_confound :
    -- Georgian MU is bound, Hungarian MU is free
    georgian.muBoundness = some .bound ∧
    hungarian.muBoundness = some .free ∧
    -- Georgian children found J-MU significantly harder
    georgianChild_j_vs_jmu.significant = true ∧
    -- Hungarian: no significant sentence-type effect on replays
    (hungarianSentencePlayedLRT.filter
      (·.effect == "sentence")).all (·.significant == false) = true := by
  native_decide

/--
**Open problem: predict the @cite{bill-etal-2025} acquisition asymmetry.**

No existing account predicts the full cross-linguistic pattern:
- @cite{mitrovic-sauerland-2016} + Transparency Principle → predicts J-MU easiest. Wrong for Georgian.
- @cite{szabolcsi-2015} → alternative quantifier-particle analysis. Doesn't predict it.
- @cite{haslinger-etal-2019} → plural/distributive analysis. Doesn't predict it.

A complete theory should derive: when MU is morphologically bound, J-MU
incurs extra acquisition cost (segmentation difficulty outweighs transparency
benefit). When MU is free, no such cost arises, yielding the Hungarian null.

TODO: This likely requires a processing/acquisition model where morphological
complexity (boundness) and syntactic transparency (overt form-meaning mapping)
are competing factors. The `sorry` marks this as the central open gap in the
coordination typology — the M&S categories describe the space but don't yet
predict which regions are hard to acquire.
-/
theorem predict_acquisition_asymmetry
    (sys : ConjunctionSystem)
    (h_all : hasAllThreeStrategies sys = true)
    (h_bound : sys.muBoundness = some .bound) :
    -- When MU is bound and all three strategies exist,
    -- J-MU should be predicted harder than J-only.
    -- (This is what Georgian shows and what no current theory derives.)
    -- TODO: State a real prediction (e.g., J-MU processing cost > J-only cost)
    True := trivial

-- ============================================================================
-- WALS Coordination Features (Chapters 56, 63, 64)
-- ============================================================================

-- ============================================================================
-- Chapter 56: Conjunctions and Universal Quantifiers
-- ============================================================================

/-- WALS Ch 56: Whether a language's conjunction marker is formally similar
    to its universal quantifier and/or interrogative pronoun.

    This captures a deep typological pattern: in many languages, "and",
    "all/every", and "what/who" share morphological material, suggesting
    a common semantic core (set-theoretic operations over individuals). -/
inductive ConjQuantRelation where
  /-- Conjunction and universal quantifier are formally unrelated.
      Example: English "and" vs "every/all". -/
  | formallyDifferent
  /-- Conjunction and universal quantifier share formal material, but
      the interrogative pronoun is different.
      Example: English "every" ~ "and" similarity is marginal; Hungarian
      "es" (and) ~ "minden" (every) share no form but the quantifier
      and interrogative are linked. -/
  | similarNoInterrogative
  /-- Conjunction, universal quantifier, and interrogative pronoun all
      share formal material.
      Example: Japanese "mo" serves as conjunction particle ("A-mo B-mo"),
      universal quantifier ("dare-mo" = everyone), and is related to
      the interrogative "dare" (who). -/
  | similarWithInterrogative
  deriving DecidableEq, Repr

-- ============================================================================
-- Chapter 63: Noun Phrase Conjunction
-- ============================================================================

/-- WALS Ch 63: Whether a language's NP coordinator ("and") is formally
    identical to its comitative adposition ("with").

    This is directly relevant to the diachronic source of coordinators:
    languages where "and" = "with" are those where the comitative-to-
    coordinator grammaticalization pathway is still transparent. -/
inductive ConjComitativeRelation where
  /-- The conjunction marker and comitative marker are different forms.
      Example: English "and" (conjunction) vs "with" (comitative). -/
  | andDifferentFromWith
  /-- The conjunction marker and comitative marker are the same form.
      Example: Japanese "to" serves as both comitative ("with") and
      conjunction ("and"); Swahili "na" means both "and" and "with". -/
  | andIdenticalToWith
  deriving DecidableEq, Repr

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

/-- WALS Ch 64: Whether a language uses the same conjunction marker for
    NP coordination ("cats and dogs") and VP/clausal coordination
    ("sang and danced").

    Languages that differentiate may use distinct markers, or may use
    overt coordination for one but juxtaposition for the other. -/
inductive NomVerbalConjRelation where
  /-- Same conjunction marker for NP and VP coordination.
      Example: English "and" in both "cats and dogs" and "sang and danced". -/
  | identity
  /-- Different conjunction markers for NP and VP coordination.
      Example: Japanese "to" for NPs ("inu to neko") but different
      strategies for VP conjunction. -/
  | differentiation
  /-- Both NP and VP coordination are expressed by juxtaposition (no
      overt marker for either).
      Example: some Australian and South American languages. -/
  | bothJuxtaposition
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

/-- Map WALS F56A to our `ConjQuantRelation`. -/
private def fromWALS56A : Core.WALS.F56A.ConjunctionsAndUniversalQuantifiers → ConjQuantRelation
  | .formallyDifferent => .formallyDifferent
  | .formallySimilarWithoutInterrogative => .similarNoInterrogative
  | .formallySimilarWithInterrogative => .similarWithInterrogative

/-- Map WALS F63A to our `ConjComitativeRelation`. -/
private def fromWALS63A : Core.WALS.F63A.NounPhraseConjunction → ConjComitativeRelation
  | .andDifferentFromWith => .andDifferentFromWith
  | .andIdenticalToWith => .andIdenticalToWith

/-- Map WALS F64A to our `NomVerbalConjRelation`. -/
private def fromWALS64A : Core.WALS.F64A.NominalAndVerbalConjunction → NomVerbalConjRelation
  | .identity => .identity
  | .differentiation => .differentiation
  | .bothExpressedByJuxtaposition => .bothJuxtaposition

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
  , conjQuant := some .similarNoInterrogative
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
  , conjQuant := some .similarWithInterrogative
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
  , conjQuant := some .similarWithInterrogative
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
  , conjQuant := some .similarWithInterrogative
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'ja' for both NP and VP; comitative expressed by " ++
                 "case suffix, not 'ja'; conjunction-quantifier-" ++
                 "interrogative formally linked" }

/--
Hungarian (Uralic).
Ch 56: Conjunction and universal quantifier formally similar without
  interrogative link.
Ch 63: "es" (and) is different from comitative "-val, -vel" (with).
Ch 64: Same "es" for NP and VP coordination (identity).
-/
def hungarianWALS : CoordinationProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , family := "Uralic"
  , conjQuant := some .similarNoInterrogative
  , conjComitative := some .andDifferentFromWith
  , nomVerbalConj := some .identity
  , walsNotes := "'es' for both NP and VP; distinct from comitative " ++
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
  , conjQuant := some .similarWithInterrogative
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
  , conjQuant := some .similarWithInterrogative
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
    (Core.WALS.F56A.lookup "eng").map (fromWALS56A ·.value) =
    englishWALS.conjQuant := by native_decide
theorem french_f56a :
    (Core.WALS.F56A.lookup "fre").map (fromWALS56A ·.value) =
    frenchWALS.conjQuant := by native_decide
theorem japanese_f56a :
    (Core.WALS.F56A.lookup "jpn").map (fromWALS56A ·.value) =
    japaneseWALS.conjQuant := by native_decide
theorem mandarin_f56a :
    (Core.WALS.F56A.lookup "mnd").map (fromWALS56A ·.value) =
    mandarinWALS.conjQuant := by native_decide
theorem turkish_f56a :
    (Core.WALS.F56A.lookup "tur").map (fromWALS56A ·.value) =
    turkishWALS.conjQuant := by native_decide
theorem finnish_f56a :
    (Core.WALS.F56A.lookup "fin").map (fromWALS56A ·.value) =
    finnishWALS.conjQuant := by native_decide
theorem hungarian_f56a :
    (Core.WALS.F56A.lookup "hun").map (fromWALS56A ·.value) =
    hungarianWALS.conjQuant := by native_decide
theorem hindi_f56a :
    (Core.WALS.F56A.lookup "hin").map (fromWALS56A ·.value) =
    hindiWALS.conjQuant := by native_decide
theorem tagalog_f56a :
    (Core.WALS.F56A.lookup "tag").map (fromWALS56A ·.value) =
    tagalogWALS.conjQuant := by native_decide

-- F63A grounding (14 languages present; German absent)
theorem english_f63a :
    (Core.WALS.F63A.lookup "eng").map (fromWALS63A ·.value) =
    englishWALS.conjComitative := by native_decide
theorem french_f63a :
    (Core.WALS.F63A.lookup "fre").map (fromWALS63A ·.value) =
    frenchWALS.conjComitative := by native_decide
theorem spanish_f63a :
    (Core.WALS.F63A.lookup "spa").map (fromWALS63A ·.value) =
    spanishWALS.conjComitative := by native_decide
theorem russian_f63a :
    (Core.WALS.F63A.lookup "rus").map (fromWALS63A ·.value) =
    russianWALS.conjComitative := by native_decide
theorem japanese_f63a :
    (Core.WALS.F63A.lookup "jpn").map (fromWALS63A ·.value) =
    japaneseWALS.conjComitative := by native_decide
theorem mandarin_f63a :
    (Core.WALS.F63A.lookup "mnd").map (fromWALS63A ·.value) =
    mandarinWALS.conjComitative := by native_decide
theorem korean_f63a :
    (Core.WALS.F63A.lookup "kor").map (fromWALS63A ·.value) =
    koreanWALS.conjComitative := by native_decide
theorem turkish_f63a :
    (Core.WALS.F63A.lookup "tur").map (fromWALS63A ·.value) =
    turkishWALS.conjComitative := by native_decide
theorem finnish_f63a :
    (Core.WALS.F63A.lookup "fin").map (fromWALS63A ·.value) =
    finnishWALS.conjComitative := by native_decide
theorem hungarian_f63a :
    (Core.WALS.F63A.lookup "hun").map (fromWALS63A ·.value) =
    hungarianWALS.conjComitative := by native_decide
theorem hindi_f63a :
    (Core.WALS.F63A.lookup "hin").map (fromWALS63A ·.value) =
    hindiWALS.conjComitative := by native_decide
theorem arabic_f63a :
    (Core.WALS.F63A.lookup "aeg").map (fromWALS63A ·.value) =
    arabicWALS.conjComitative := by native_decide
theorem swahili_f63a :
    (Core.WALS.F63A.lookup "swa").map (fromWALS63A ·.value) =
    swahiliWALS.conjComitative := by native_decide
theorem tagalog_f63a :
    (Core.WALS.F63A.lookup "tag").map (fromWALS63A ·.value) =
    tagalogWALS.conjComitative := by native_decide

-- F64A grounding (14 languages present; Swahili absent)
theorem english_f64a :
    (Core.WALS.F64A.lookup "eng").map (fromWALS64A ·.value) =
    englishWALS.nomVerbalConj := by native_decide
theorem german_f64a :
    (Core.WALS.F64A.lookup "ger").map (fromWALS64A ·.value) =
    germanWALS.nomVerbalConj := by native_decide
theorem french_f64a :
    (Core.WALS.F64A.lookup "fre").map (fromWALS64A ·.value) =
    frenchWALS.nomVerbalConj := by native_decide
theorem spanish_f64a :
    (Core.WALS.F64A.lookup "spa").map (fromWALS64A ·.value) =
    spanishWALS.nomVerbalConj := by native_decide
theorem russian_f64a :
    (Core.WALS.F64A.lookup "rus").map (fromWALS64A ·.value) =
    russianWALS.nomVerbalConj := by native_decide
theorem japanese_f64a :
    (Core.WALS.F64A.lookup "jpn").map (fromWALS64A ·.value) =
    japaneseWALS.nomVerbalConj := by native_decide
theorem mandarin_f64a :
    (Core.WALS.F64A.lookup "mnd").map (fromWALS64A ·.value) =
    mandarinWALS.nomVerbalConj := by native_decide
theorem korean_f64a :
    (Core.WALS.F64A.lookup "kor").map (fromWALS64A ·.value) =
    koreanWALS.nomVerbalConj := by native_decide
theorem turkish_f64a :
    (Core.WALS.F64A.lookup "tur").map (fromWALS64A ·.value) =
    turkishWALS.nomVerbalConj := by native_decide
theorem finnish_f64a :
    (Core.WALS.F64A.lookup "fin").map (fromWALS64A ·.value) =
    finnishWALS.nomVerbalConj := by native_decide
theorem hungarian_f64a :
    (Core.WALS.F64A.lookup "hun").map (fromWALS64A ·.value) =
    hungarianWALS.nomVerbalConj := by native_decide
theorem hindi_f64a :
    (Core.WALS.F64A.lookup "hin").map (fromWALS64A ·.value) =
    hindiWALS.nomVerbalConj := by native_decide
theorem arabic_f64a :
    (Core.WALS.F64A.lookup "aeg").map (fromWALS64A ·.value) =
    arabicWALS.nomVerbalConj := by native_decide
theorem tagalog_f64a :
    (Core.WALS.F64A.lookup "tag").map (fromWALS64A ·.value) =
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
