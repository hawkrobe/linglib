import Linglib.Typology.Coordination
import Linglib.Fragments.Georgian.Coordination
import Linglib.Fragments.Hungarian.Coordination
import Linglib.Fragments.Latin.Coordination
import Linglib.Fragments.Irish.Coordination
import Linglib.Fragments.Japanese.Coordination
import Linglib.Fragments.German.Coordination

/-!
# Haspelmath (2007): Coordination — structural typology
@cite{haspelmath-2007} @cite{stassen-2000} @cite{mitrovic-sauerland-2014}
@cite{mitrovic-sauerland-2016} @cite{mitrovic-2021} @cite{noonan-1992}
@cite{schwartz-1989} @cite{rowlands-1969} @cite{sridhar-1990}
@cite{dench-1995} @cite{beyer-1992}

Martin Haspelmath. "Coordination." In *Language Typology and Syntactic
Description, Vol. II*, ed. T. Shopen, 2007.

Cross-linguistic typology of coordination: syndesis (asyndetic /
monosyndetic / bisyndetic), structural patterns, and diachronic sources
(comitative vs additive focus particle).

## What lives here

- The 19-language exemplar sample (M&S focus + Haspelmath illustrations).
- Structural / diachronic generalisations
  (`comitative_source_monosyndetic`, `focus_particle_source_bisyndetic`).
- @cite{mitrovic-sauerland-2016} M&S generalisations
  (`mu_additive_generalization`, `j_is_universal`, `all_three_is_rare`,
  `mu_boundness_asymmetry`).

The structural enums (`Syndesis`, `CoordPattern`, `DiachronicSource`,
etc.) live in the substrate `Linglib/Typology/Coordination.lean`.

## Sample composition

The 19 languages combine:
- **M&S focus languages** (English, Japanese, Hungarian, Georgian, Latin,
  Korean, Slovenian) where the J/MU/J-MU semantic decomposition is the
  primary motivation.
- **Haspelmath structural exemplars** (Lango, Hausa, Yoruba, Kannada,
  Martuthunira, Classical Tibetan, Hindi-Urdu, Turkish, Irish, Persian,
  Finnish, German) covering each structural pattern.
-/

set_option autoImplicit false

namespace Phenomena.Coordination.Studies.Haspelmath2007

open Typology.Coordination
open Features.Coordination

-- ============================================================================
-- §1. M&S focus languages (Bill et al. 2025 / Mitrović & Sauerland 2016)
-- ============================================================================

/-- English only has J ("and"). "Both...and" is sometimes analyzed as J-MU,
    but "both" is not productively used as an additive particle (*"John both
    slept") and English lacks MU-only conjunction (*"John both Mary both slept"). -/
def english : ConjunctionSystem :=
  { language := "English"
  , morphemes :=
    [ { entry := { form := "and", gloss := "and", role := .j, boundness := .free } } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "eng" }

/-- German uses "und" (J, free word), like English "and". J-only strategy.
    Test language for @cite{schwarzer-2026}'s study of selection-violating
    coordination in OV environments. -/
def german : ConjunctionSystem :=
  { language := "German"
  , morphemes :=
    [ { entry := Fragments.German.Coordination.und } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "deu" }

/-- Japanese conjunction uses "to" (J) and "mo" (MU).
    "to" derives from the comitative marker. "mo" is also the additive particle. -/
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

/-- Hungarian: "és" (J, free, prepositive), "is" (MU, free, postpositive).
    "is" is also the additive focus particle ("also").
    One of two languages in the sample with all three strategies (J, MU, J-MU). -/
def hungarian : ConjunctionSystem :=
  { language := "Hungarian"
  , morphemes :=
    [ { entry := Fragments.Hungarian.Coordination.es }
    , { entry := Fragments.Hungarian.Coordination.is_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "hun" }

/-- Georgian: "da" (J, free), "-c" (MU, bound clitic).
    "-c" is also the additive/focus particle. -/
def georgian : ConjunctionSystem :=
  { language := "Georgian"
  , morphemes :=
    [ { entry := Fragments.Georgian.Coordination.da }
    , { entry := Fragments.Georgian.Coordination.c_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "kat" }

/-- Latin: "et" (J, free, prepositive) and "-que" (MU, bound enclitic, postpositive).
    "-que" is the classic bound MU particle. Three patterns: A et B,
    A B-que, et A B-que. -/
def latin : ConjunctionSystem :=
  { language := "Latin"
  , morphemes :=
    [ { entry := Fragments.Latin.Coordination.et }
    , { entry := Fragments.Latin.Coordination.que
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a_b'co, .co'a_b'co]
  , iso := "lat" }

/-- Korean: "-(i)rang" (J, bound, postpositive) and "-to" (MU, bound, additive). -/
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

/-- Slovenian: "in" (J, free, prepositive). Primarily J-only. -/
def slovenian : ConjunctionSystem :=
  { language := "Slovenian"
  , morphemes :=
    [ { entry := { form := "in", gloss := "and", role := .j, boundness := .free } } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "slv" }

-- ============================================================================
-- §2. Haspelmath 2007 structural exemplars
-- ============================================================================

/-- Lango (Nilotic, Uganda): "kèdè" is a comitative marker that also serves
    as coordinator. Classic AND-language with comitative source giving
    monosyndetic A co-B (@cite{noonan-1992}:163, @cite{haspelmath-2007} (20)). -/
def lango : ConjunctionSystem :=
  { language := "Lango"
  , morphemes :=
    [ { entry := { form := "kèdè", gloss := "and; with", role := .j, boundness := .free }
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "laj" }

/-- Hausa (Chadic, Nigeria): "da" means both "with" (comitative) and "and"
    (conjunction) (@cite{schwartz-1989}:32,36; @cite{haspelmath-2007} (12)). -/
def hausa : ConjunctionSystem :=
  { language := "Hausa"
  , morphemes :=
    [ { entry := { form := "da", gloss := "and; with", role := .j, boundness := .free }
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "hau" }

/-- Yoruba (Kwa, Nigeria): "àtí" in "àtí A àtí B" — canonical prepositive
    bisyndetic coordination (@cite{rowlands-1969}:201ff, @cite{haspelmath-2007} (25)). -/
def yoruba : ConjunctionSystem :=
  { language := "Yoruba"
  , morphemes :=
    [ { entry := { form := "àtí", gloss := "and", role := .j, boundness := .free } } ]
  , strategies := [.jOnly]
  , patterns := [.co'a_co'b]
  , iso := "yor" }

/-- Kannada (Dravidian): postpositive "-u" on each coordinand gives A-co B-co
    (@cite{sridhar-1990}:106, @cite{haspelmath-2007} (5)). "-u" is also the
    Dravidian additive/focus particle. -/
def kannada : ConjunctionSystem :=
  { language := "Kannada"
  , morphemes :=
    [ { entry := { form := "-u", gloss := "and; also", role := .mu, boundness := .bound
                 , alsoAdditive := true }
      , source := some .focusParticle } ]
  , strategies := [.muOnly]
  , patterns := [.a'co_b'co]
  , iso := "kan" }

/-- Martuthunira (Pama-Nyungan, W. Australia): "-thurti" on each coordinand
    gives A-co B-co (@cite{dench-1995}:98, @cite{haspelmath-2007} (26)). -/
def martuthunira : ConjunctionSystem :=
  { language := "Martuthunira"
  , morphemes :=
    [ { entry := { form := "-thurti", gloss := "and", role := .j, boundness := .bound } } ]
  , strategies := [.jOnly]
  , patterns := [.a'co_b'co]
  , iso := "vma" }

/-- Classical Tibetan: "-daŋ" is postpositive on first coordinand, giving A-co B.
    Derives from comitative source (@cite{beyer-1992}:240, @cite{haspelmath-2007} (21)). -/
def classicalTibetan : ConjunctionSystem :=
  { language := "Classical Tibetan"
  , morphemes :=
    [ { entry := { form := "-daŋ", gloss := "and; with", role := .j, boundness := .bound }
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a'co_b]
  , iso := "xct" }

/-- Hindi-Urdu: "aur" (J, free, prepositive) and "bhii" (MU, free, additive).
    Pattern: A aur B (monosyndetic), A bhii B bhii (bisyndetic postpositive). -/
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

/-- Turkish: "ve" (J, free, prepositive) and "de/da" (MU, free, additive). -/
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

/-- Irish: "agus" (J, free, prepositive). Pattern: A agus B (monosyndetic medial). -/
def irish : ConjunctionSystem :=
  { language := "Irish"
  , morphemes :=
    [ { entry := Fragments.Irish.Coordination.agus } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "gle" }

/-- Persian: "va" (J, free, prepositive) and "ham" (MU, free, additive). -/
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

/-- Finnish: "ja" (J, free, prepositive) and "-kin" (MU, bound, additive).
    *koira-kin kissa-kin* 'dog-too cat-too' = 'both the dog and the cat'. -/
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

/-- All 19 ConjunctionSystem profiles. -/
def allLanguages : List ConjunctionSystem :=
  [ english, german, japanese, hungarian, georgian, latin, korean, slovenian
  , lango, hausa, yoruba, kannada, martuthunira, classicalTibetan
  , hindiUrdu, turkish, irish, persian, finnish ]

/-- M&S focus languages (Bill et al. 2025 acquisition study sample). -/
def msLanguages : List ConjunctionSystem :=
  [english, japanese, hungarian, georgian, latin, korean, slovenian]

-- ============================================================================
-- §3. Sample-level statistics
-- ============================================================================

theorem sample_size : allLanguages.length = 19 := by native_decide

theorem ms_sample_size : msLanguages.length = 7 := by native_decide

-- ============================================================================
-- §4. M&S generalisations (Mitrović & Sauerland 2016)
-- ============================================================================

/-- Every language with a MU conjunction particle uses the same morpheme
    as its additive ("also/too") particle. Core M&S prediction: MU is a
    single lexical item with subset semantics that appears in both
    conjunction and additive contexts. -/
theorem mu_additive_generalization :
    let withMu := allLanguages.filter fun sys =>
      sys.morphemes.any (·.entry.role == .mu)
    withMu.all (·.muIsAdditive) = true := by
  native_decide

/-- Every M&S-classified language has at least the J-only strategy. -/
theorem j_is_universal :
    msLanguages.all (·.hasStrategy .jOnly) = true := by
  native_decide

/-- Helper: does the system attest all three strategies (J, MU, J-MU)? -/
def hasAllThreeStrategies (sys : ConjunctionSystem) : Bool :=
  sys.hasStrategy .jOnly && sys.hasStrategy .muOnly && sys.hasStrategy .jMu

/-- All three strategies (J, MU, J-MU) are attested only in Georgian and
    Hungarian in the sample. Typologically rare. -/
theorem all_three_is_rare :
    let count := (allLanguages.filter hasAllThreeStrategies).length
    count == 2 := by native_decide

/-- Georgian MU is bound, Hungarian MU is free. @cite{bill-etal-2025}
    @cite{mitrovic-2021} speculate this morphological difference may explain
    the acquisition asymmetry: bound morphemes are harder to segment. -/
theorem mu_boundness_asymmetry :
    georgian.muBoundness = some .bound ∧
    hungarian.muBoundness = some .free := by
  native_decide

-- ============================================================================
-- §5. Haspelmath structural / diachronic generalisations
-- ============================================================================

/-- Every language with a known comitative-sourced morpheme has at least
    one monosyndetic structural pattern. Confirms: comitative "with" →
    monosyndetic A co-B / A-co B. Languages: Lango, Hausa, Japanese,
    Classical Tibetan. -/
theorem comitative_source_monosyndetic :
    let withComitative := allLanguages.filter (·.hasSource .comitative)
    withComitative.all (·.hasMonosyndetic) = true := by
  native_decide

/-- Every language with a known focus-particle-sourced morpheme has at least
    one bisyndetic structural pattern. Confirms: additive focus particle
    "also" → bisyndetic A-co B-co. Languages: Japanese, Hungarian, Georgian,
    Latin, Korean, Kannada. -/
theorem focus_particle_source_bisyndetic :
    let withFocusParticle := allLanguages.filter (·.hasSource .focusParticle)
    withFocusParticle.all (·.hasBisyndetic) = true := by
  native_decide

end Phenomena.Coordination.Studies.Haspelmath2007
