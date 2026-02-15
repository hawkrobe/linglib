/-
# Cross-Linguistic Typology of Coordination

Two complementary typological frameworks for coordination:

## 1. Structural Typology (Haspelmath 2007)

Classifies coordination by overt form:
- **Syndesis**: asyndetic (A B), monosyndetic (A co-B), bisyndetic (co-A co-B)
- **Coordinator position**: prepositive (co-A) vs postpositive (A-co)
- **Universal gap**: the pattern co-A B is unattested (Stassen 2000, n=260)
- **Diachronic sources**: comitative ("with") → monosyndetic J;
  additive focus particle ("also") → bisyndetic MU

## 2. Semantic Decomposition (Mitrović & Sauerland 2014, 2016)

Classifies by underlying semantic structure:
- J (set intersection) + MU (subset/additive) + ☉ (type-shifter)
- Languages vary in which pieces are overtly realized

## Connection

Haspelmath's structural categories map onto M&S's semantic pieces:
- Monosyndetic medial (A co-B) = J-only (comitative source)
- Bisyndetic postpositive (A-co B-co) = MU-only (focus particle source)
- Bisyndetic mixed (co-A co-B, A-co co-B) = J-MU (both sources)

The MU particle in conjunction is typically the SAME morpheme as the
language's additive/focus particle, confirming the diachronic link.

## References

- Haspelmath (2007). Coordination. In Shopen (ed.), Language Typology
  and Syntactic Description. Cambridge University Press.
- Stassen (2000). AND-languages and WITH-languages. Linguistic Typology 4.
- Mitrović & Sauerland (2014). Decomposing coordination. NELS 44.
- Mitrović & Sauerland (2016). Two conjunctions are better than one.
  Acta Linguistica Hungarica 63(4), 471-494.
- Mitrović (2021). Superparticles. Springer. (SNLT 98)
- Bill et al. (2025). Is DP conjunction always complex? S&P 18(5).
-/

import Linglib.Phenomena.Coordination.Studies.BillEtAl2025

namespace Phenomena.Coordination.Typology

open Phenomena.Coordination.Studies.BillEtAl2025

-- ============================================================================
-- Haspelmath (2007): Structural Typology
-- ============================================================================

/-- Syndesis: presence and number of overt coordinators (Haspelmath §1). -/
inductive Syndesis where
  | asyndetic      -- A B (juxtaposition, no overt linker)
  | monosyndetic   -- A co-B (single coordinator)
  | bisyndetic     -- co-A co-B (two coordinators, one per coordinand)
  deriving DecidableEq, BEq, Repr

/--
Coordinator position relative to its coordinand (Haspelmath §1.2).

Haspelmath notes that **co-A B (prepositive on first coordinand only)
is unattested** across 260 languages (Stassen 2000). This is the one
logically possible monosyndetic pattern that never occurs.
-/
inductive CoordinatorPosition where
  | prepositive    -- co precedes coordinand: "and A" / English "both X"
  | postpositive   -- co follows coordinand: "A-and" / Latin "X-que"
  deriving DecidableEq, BEq, Repr

/--
Structural pattern for binary coordination (Haspelmath (17)).

Monosyndetic: 3 attested patterns (of 4 logically possible).
  A co-B  (prepositive on 2nd: English "A and B")
  A-co B  (postpositive on 1st: Tibetan "A-daŋ B")
  A B-co  (postpositive on 2nd: Latin "A B-que")

  co-A B  — UNATTESTED (Stassen 2000, n=260 languages)

Bisyndetic: 4 attested patterns.
  co-A co-B   (prepositive: Yoruba "àtí A àtí B")
  A-co B-co   (postpositive: Martuthunira "A-thurti B-thurti")
  A-co co-B   (mixed: Homeric Greek "A-te kaì B")
  co-A B-co   (mixed: Latin "et A B-que")
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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
Relevant to acquisition (Clark 2017: free morphemes acquired more readily).
-/
inductive Boundness where
  | free    -- independent word (Hungarian "is", English "and")
  | bound   -- clitic or suffix (Georgian "-c", Latin "-que")
  deriving DecidableEq, BEq, Repr

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
-- Language Data: Haspelmath (2007) Typological Examples
-- ============================================================================

/--
Lango (Nilotic, Uganda): "kèdè" is a comitative marker ("with") that also
serves as coordinator ("and"). The classic AND-language: comitative source
gives monosyndetic A co-B (Noonan 1992:163, Haspelmath 2007: (20)).
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
(Schwartz 1989:32,36; Haspelmath 2007: (12)).
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
(Rowlands 1969:201ff, Haspelmath 2007: (25)).
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
gives A-co B-co (Sridhar 1990:106, Haspelmath 2007: (5)).
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
gives A-co B-co (Dench 1995:98, Haspelmath 2007: (26)).
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
Derives from comitative source (Beyer 1992:240, Haspelmath 2007: (21)).
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

def allLanguages : List ConjunctionSystem :=
  [ english, japanese, hungarian, georgian, latin, korean, slovenian
  , lango, hausa, yoruba, kannada, martuthunira, classicalTibetan
  , hindiUrdu, turkish, irish, persian ]

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

/-- Languages with full M&S strategy classification (from Bill et al. 2025). -/
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

Bill et al. (2025) speculate this morphological difference may explain
why Georgian children found MU-involving expressions harder than
Hungarian children did: bound morphemes are harder to segment and acquire
(Clark 2017).
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

M&S (2014, 2016) claim that EVERY language has the same underlying structure
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
**Empirical challenge to M&S universality (Bill et al. 2025).**

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
**The boundness confound (Bill et al. 2025, §5).**

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
**Open problem: predict the Bill et al. (2025) acquisition asymmetry.**

No existing account predicts the full cross-linguistic pattern:
- M&S (2016) + Transparency Principle → predicts J-MU easiest. Wrong for Georgian.
- Szabolcsi (2015) → alternative quantifier-particle analysis. Doesn't predict it.
- Haslinger et al. (2019) → plural/distributive analysis. Doesn't predict it.

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

end Phenomena.Coordination.Typology
