import Linglib.Syntax.Coordination
import Linglib.Fragments.English.Coordination
import Linglib.Fragments.Farsi.Coordination
import Linglib.Fragments.Finnish.Coordination
import Linglib.Fragments.Georgian.Coordination
import Linglib.Fragments.German.Coordination
import Linglib.Fragments.Hausa.Coordination
import Linglib.Fragments.HindiUrdu.Coordination
import Linglib.Fragments.Hungarian.Coordination
import Linglib.Fragments.Irish.Coordination
import Linglib.Fragments.Japanese.Coordination
import Linglib.Fragments.Kannada.Coordination
import Linglib.Fragments.Korean.Coordination
import Linglib.Fragments.Lango.Coordination
import Linglib.Fragments.Latin.Coordination
import Linglib.Fragments.Tibetan.Coordination
import Linglib.Fragments.Turkish.Coordination
import Linglib.Fragments.Yoruba.Coordination

/-!
# Haspelmath (2007): Coordination — structural typology
[haspelmath-2007] [stassen-2000] [noonan-1992] [schwartz-1989]
[rowlands-1969] [sridhar-1990] [dench-1995] [beyer-1992]
[kornfilt-1997]

Martin Haspelmath. "Coordination." In *Language Typology and Syntactic
Description, Vol. II*, ed. T. Shopen, 2007.

Cross-linguistic typology of coordination — restricted here to **conjunctive**
coordination. The chapter as a whole covers four semantic types (conjunction,
disjunction, adversative, causal) plus emphatic and emphatic-negative variants;
the formalisation below engages only conjunction (§1 *Types and positions of
coordinators*, §5.1 *Diachronic sources*). Disjunction (§4), adversative,
causal, ellipsis (§6), and subordination diagnostics (§7) are out of scope.

The companion file `Studies/MitrovicSauerland2016.lean` consumes the
language sample below to formalise the J-μ predictions; the `iso` and
`patterns` data sets are shared.

## Main declarations

* `allLanguages` — 19-language sample (Haspelmath structural exemplars + M&S
  focus languages).
* `msLanguages` — M&S-focused sub-sample of 7 languages; consumed by
  `MitrovicSauerland2016.lean`.
* `coAB_unattested` — Haspelmath's structural generalisation that the
  monosyndetic pattern `co-A B` (prepositive on first coordinand only) is
  typologically absent (cf. [stassen-2000], n=260).
* `comitative_source_monosyndetic`, `focus_particle_source_bisyndetic` —
  the two diachronic-source / syndesis correlations Haspelmath proposes
  in §5.1.

## Implementation notes

* Records use the `ConjunctionSystem` struct from
  `Typology/Coordination.lean`. All morphemes reference Fragment entries
  except for Slovenian (*in*) and Martuthunira (*-thurti*), which remain
  inline since the project has no `Fragments/{Slovenian,Martuthunira}/`
  directory and creating one for a single morpheme is overkill.
* Pattern data follow the cited primary sources, *not* the M&S analyses
  layered on top — e.g., Turkish *de* is monosyndetic postpositive per
  [haspelmath-2007] (23), not bisyndetic.
-/

namespace Haspelmath2007

open Syntax.Coordination
/-! ### M&S focus languages -/

/-- English only has J ("and"). "Both...and" is sometimes analyzed as J-MU,
    but "both" is not productively used as an additive particle (*"John both
    slept") and English lacks MU-only conjunction (*"John both Mary both slept"). -/
def english : ConjunctionSystem :=
  { language := "English"
  , morphemes := [ { entry := English.Coordination.and_ } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "eng" }

/-- German uses "und" (J, free word), like English "and". J-only strategy. -/
def german : ConjunctionSystem :=
  { language := "German"
  , morphemes :=
    [ { entry := German.Coordination.und } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "deu" }

/-- Japanese conjunction uses "to" (J) and "mo" (MU).
    "to" derives from the comitative marker. "mo" is also the additive particle. -/
def japanese : ConjunctionSystem :=
  { language := "Japanese"
  , morphemes :=
    [ { entry := Japanese.Coordination.to_
      , source := some .comitative }
    , { entry := Japanese.Coordination.mo
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a'co_b, .a'co_b'co]
  , iso := "jpn" }

/-- Hungarian: "és" (J, free, prepositive), "is" (MU, free, postpositive).
    "is" is also the additive focus particle ("also").
    One of the languages in the M&S 2016 sample exhibiting triadic exponency
    (all three of two μ heads + J head) — see [mitrovic-sauerland-2016]
    (28). -/
def hungarian : ConjunctionSystem :=
  { language := "Hungarian"
  , morphemes :=
    [ { entry := Hungarian.Coordination.es }
    , { entry := Hungarian.Coordination.is_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "hun" }

/-- Georgian: "da" (J, free), "-c" (MU, bound clitic).
    "-c" is also the additive/focus particle. Classified as exhibiting all
    three M&S strategies per [mitrovic-2021]; [mitrovic-sauerland-2016]
    itself uses SE Macedonian, Hungarian, and Avar as the triadic-exponency
    languages — Georgian's inclusion here is from the later literature. -/
def georgian : ConjunctionSystem :=
  { language := "Georgian"
  , morphemes :=
    [ { entry := Georgian.Coordination.da }
    , { entry := Georgian.Coordination.c_
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
    [ { entry := Latin.Coordination.et }
    , { entry := Latin.Coordination.que
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a_b'co, .co'a_b'co]
  , iso := "lat" }

/-- Korean: "-(i)rang" (J, bound, postpositive) and "-to" (MU, bound, additive).
    Not discussed in [haspelmath-2007]; classification follows
    [mitrovic-2021]. -/
def korean : ConjunctionSystem :=
  { language := "Korean"
  , morphemes :=
    [ { entry := Korean.Coordination.irang }
    , { entry := Korean.Coordination.to_
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

/-! ### Haspelmath 2007 structural exemplars -/

/-- Lango (Nilotic, Uganda): "kèdè" is a comitative marker that also serves
    as coordinator. Classic AND-language with comitative source giving
    monosyndetic A co-B ([noonan-1992]:163, [haspelmath-2007] (20)). -/
def lango : ConjunctionSystem :=
  { language := "Lango"
  , morphemes :=
    [ { entry := Lango.Coordination.kede
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "laj" }

/-- Hausa (Chadic, Nigeria): "da" means both "with" (comitative) and "and"
    (conjunction) ([schwartz-1989]:32,36; [haspelmath-2007] (12)). -/
def hausa : ConjunctionSystem :=
  { language := "Hausa"
  , morphemes :=
    [ { entry := Hausa.Coordination.da
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "hau" }

/-- Yoruba (Kwa, Nigeria): "àtí" in "àtí A àtí B" — canonical prepositive
    bisyndetic coordination ([rowlands-1969]:201ff, [haspelmath-2007] (25)). -/
def yoruba : ConjunctionSystem :=
  { language := "Yoruba"
  , morphemes := [ { entry := Yoruba.Coordination.ati } ]
  , strategies := [.jOnly]
  , patterns := [.co'a_co'b]
  , iso := "yor" }

/-- Kannada (Dravidian): postpositive "-u" on each coordinand gives A-co B-co
    ([sridhar-1990]:106, [haspelmath-2007] (5)). "-u" is also the
    Dravidian additive/focus particle. -/
def kannada : ConjunctionSystem :=
  { language := "Kannada"
  , morphemes :=
    [ { entry := Kannada.Coordination.u
      , source := some .focusParticle } ]
  , strategies := [.muOnly]
  , patterns := [.a'co_b'co]
  , iso := "kan" }

/-- Martuthunira (Pama-Nyungan, W. Australia): "-thurti" on each coordinand
    gives A-co B-co ([dench-1995]:98, [haspelmath-2007] (26)). -/
def martuthunira : ConjunctionSystem :=
  { language := "Martuthunira"
  , morphemes :=
    [ { entry := { form := "-thurti", gloss := "and", role := .j, boundness := .bound } } ]
  , strategies := [.jOnly]
  , patterns := [.a'co_b'co]
  , iso := "vma" }

/-- Classical Tibetan: "-daŋ" is postpositive on first coordinand, giving A-co B.
    Derives from comitative source ([beyer-1992]:240, [haspelmath-2007] (21)). -/
def classicalTibetan : ConjunctionSystem :=
  { language := "Classical Tibetan"
  , morphemes :=
    [ { entry := Tibetan.Coordination.dang
      , source := some .comitative } ]
  , strategies := [.jOnly]
  , patterns := [.a'co_b]
  , iso := "xct" }

/-- Hindi-Urdu: "aur" (J, free, prepositive) and "bhii" (MU, free, additive).
    Pattern: A aur B (monosyndetic), A bhii B bhii (bisyndetic postpositive). -/
def hindiUrdu : ConjunctionSystem :=
  { language := "Hindi-Urdu"
  , morphemes :=
    [ { entry := HindiUrdu.Coordination.aur }
    , { entry := HindiUrdu.Coordination.bhii
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "hin" }

/-- Turkish: "ve" (J, free, prepositive) and "de" (MU, bound enclitic,
    postpositive on first word of second coordinand).
    Per [haspelmath-2007] (23) citing [kornfilt-1997]:120, *de* is
    monosyndetic postpositive (A B-co); *de…de* bisyndetic also exists as a
    marked emphatic variant. -/
def turkish : ConjunctionSystem :=
  { language := "Turkish"
  , morphemes :=
    [ { entry := Turkish.Coordination.ve }
    , { entry := Turkish.Coordination.de
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a_b'co, .a'co_b'co]
  , iso := "tur" }

/-- Irish: "agus" (J, free, prepositive). Pattern: A agus B (monosyndetic medial). -/
def irish : ConjunctionSystem :=
  { language := "Irish"
  , morphemes :=
    [ { entry := Irish.Coordination.agus } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "gle" }

/-- Persian: "va" (J, free, prepositive) and "ham" (MU, free, additive). -/
def persian : ConjunctionSystem :=
  { language := "Persian"
  , morphemes :=
    [ { entry := Farsi.Coordination.va }
    , { entry := Farsi.Coordination.ham
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "fas" }

/-- Finnish: "ja" (J, free, prepositive) and "-kin" (MU, bound, additive).
    *koira-kin kissa-kin* 'dog-too cat-too' = 'both the dog and the cat'. -/
def finnish : ConjunctionSystem :=
  { language := "Finnish"
  , morphemes :=
    [ { entry := Finnish.Coordination.ja }
    , { entry := Finnish.Coordination.kin
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "fin" }

/-! ### Sample bundles -/

/-- All 19 `ConjunctionSystem` profiles. -/
def allLanguages : List ConjunctionSystem :=
  [ english, german, japanese, hungarian, georgian, latin, korean, slovenian
  , lango, hausa, yoruba, kannada, martuthunira, classicalTibetan
  , hindiUrdu, turkish, irish, persian, finnish ]

/-- M&S focus languages — the sub-sample consumed by
    `Studies/MitrovicSauerland2016.lean`. -/
def msLanguages : List ConjunctionSystem :=
  [english, japanese, hungarian, georgian, latin, korean, slovenian]

/-! ### Structural / diachronic generalisations -/

/-- [haspelmath-2007]'s key structural generalisation: the monosyndetic
    pattern `co-A B` (prepositive on first coordinand only) is unattested for
    conjunction, per [stassen-2000]'s 260-language sample. Verified over
    the 19-language sample via `List.contains`, which uses the `BEq` instance
    to sidestep `∈`'s `LawfulBEq` requirement. -/
theorem coAB_unattested :
    allLanguages.all (fun sys => ! sys.patterns.contains .co'a_b) := by decide

/-- Every language with a known comitative-sourced morpheme has at least
    one monosyndetic structural pattern. Confirms: comitative "with" →
    monosyndetic A co-B / A-co B. Languages: Lango, Hausa, Japanese,
    Classical Tibetan. -/
theorem comitative_source_monosyndetic :
    ∀ sys ∈ allLanguages, sys.hasSource .comitative → sys.hasMonosyndetic := by
  decide

/-- Every language with a known focus-particle-sourced morpheme has at least
    one bisyndetic structural pattern. Confirms: additive focus particle
    "also" → bisyndetic A-co B-co. Languages: Japanese, Hungarian, Georgian,
    Latin, Korean, Kannada. -/
theorem focus_particle_source_bisyndetic :
    ∀ sys ∈ allLanguages, sys.hasSource .focusParticle → sys.hasBisyndetic := by
  decide

end Haspelmath2007
